"""
Per-Transaction Verification Test

Verifies hardware against model after EVERY transaction to find
the exact point where divergence occurs.

Includes:
- Balance verification after each transaction
- Conservation tracking (total supply check)
- Transaction history capture
- Detailed divergence reporting
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
import random

class ExchangeModel:
    """Golden model for verification"""
    def __init__(self, num_users=1024):
        self.balances = {i: [1000000, 1000000] for i in range(num_users)}
        self.vault = [0, 0]

    def process(self, op, u_a, u_b, amt0, amt1):
        if u_a == u_b: return True
        bal_a = self.balances[u_a]
        bal_b = self.balances[u_b]
        fee0 = amt0 >> 11
        fee1 = amt1 >> 11

        if op == 0:  # Transfer
            if bal_a[0] >= (amt0 + fee0):
                bal_a[0] -= (amt0 + fee0)
                bal_b[0] += amt0
                self.vault[0] += fee0
                return True
        elif op == 1:  # Swap
            if bal_a[0] >= (amt0 + fee0) and bal_b[1] >= (amt1 + fee1):
                bal_a[0] -= (amt0 + fee0)
                bal_a[1] += amt1
                bal_b[0] += amt0
                bal_b[1] -= (amt1 + fee1)
                self.vault[0] += fee0
                self.vault[1] += fee1
                return True
        return False

    def get_total_usdc(self):
        """Calculate total USDC in system"""
        total = self.vault[0]
        for bal in self.balances.values():
            total += bal[0]
        return total

    def get_total_gpu(self):
        """Calculate total GPU in system"""
        total = self.vault[1]
        for bal in self.balances.values():
            total += bal[1]
        return total

def get_hw_balance(dut, user_id):
    """Get hardware balance for a user"""
    raw = int(dut.portfolios[user_id].value)
    return (raw & 0xFFFFFFFFFFFFFFFF, (raw >> 64) & 0xFFFFFFFFFFFFFFFF)

def get_hw_totals(dut, num_users):
    """Calculate total USDC and GPU in hardware"""
    total_usdc = int(dut.m_vault_usdc.value)
    total_gpu = int(dut.m_vault_gpu.value)

    for i in range(num_users):
        usdc, gpu = get_hw_balance(dut, i)
        total_usdc += usdc
        total_gpu += gpu

    return total_usdc, total_gpu

@cocotb.test()
async def test_find_divergence_point(dut):
    """
    Execute transactions with per-transaction verification
    to find exact divergence point
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== PER-TRANSACTION VERIFICATION: Finding Divergence Point ===")

    # Use same pattern as CRV swarm test to reproduce bug
    random.seed(42)
    NUM_USERS = 100  # Match CRV swarm
    MAX_TXS = 15000  # Run longer to catch the 10K+ bug

    # Conservation constants
    INITIAL_USDC = NUM_USERS * 1000000
    INITIAL_GPU = NUM_USERS * 1000000

    # Transaction history
    tx_history = []
    last_users = []

    divergence_found = False
    divergence_tx = None

    for tx_num in range(MAX_TXS):
        # Generate transaction with 50% hazard rate
        if len(last_users) > 0 and random.random() < 0.5:
            user_a = random.choice(last_users)
        else:
            user_a = random.randint(0, NUM_USERS - 1)

        user_b = random.randint(0, NUM_USERS - 1)
        while user_b == user_a:
            user_b = random.randint(0, NUM_USERS - 1)

        op = random.randint(0, 1)
        amt0 = random.randint(1000, 5000)
        amt1 = random.randint(1000, 3000)

        # Record transaction before execution
        tx_record = {
            'num': tx_num,
            'op': 'TRANSFER' if op == 0 else 'SWAP',
            'user_a': user_a,
            'user_b': user_b,
            'amt0': amt0,
            'amt1': amt1,
        }
        tx_history.append(tx_record)

        # Execute in hardware
        dut.s_opcode.value = op
        dut.s_user_a.value = user_a
        dut.s_user_b.value = user_b
        dut.s_amount_0.value = amt0
        dut.s_amount_1.value = amt1
        dut.s_valid.value = 1
        await RisingEdge(dut.clk)

        # Execute in model
        model_success = model.process(op, user_a, user_b, amt0, amt1)
        tx_record['success'] = model_success

        # Stop valid signal and wait for pipeline to complete
        dut.s_valid.value = 0
        # Pipeline is 2 stages, need at least 2 cycles for write to complete
        for _ in range(3):  # 3 cycles to be safe
            await RisingEdge(dut.clk)

        # VERIFY AFTER THIS TRANSACTION
        # 1. Check conservation first
        hw_total_usdc, hw_total_gpu = get_hw_totals(dut, NUM_USERS)

        if hw_total_usdc != INITIAL_USDC:
            dut._log.error(f"TX {tx_num}: CONSERVATION VIOLATED!")
            dut._log.error(f"  Total USDC: HW={hw_total_usdc} Expected={INITIAL_USDC} (diff={hw_total_usdc - INITIAL_USDC})")
            divergence_found = True
            divergence_tx = tx_num
            break

        if hw_total_gpu != INITIAL_GPU:
            dut._log.error(f"TX {tx_num}: CONSERVATION VIOLATED!")
            dut._log.error(f"  Total GPU: HW={hw_total_gpu} Expected={INITIAL_GPU} (diff={hw_total_gpu - INITIAL_GPU})")
            divergence_found = True
            divergence_tx = tx_num
            break

        # 2. Check both users' balances
        hw_usdc_a, hw_gpu_a = get_hw_balance(dut, user_a)
        hw_usdc_b, hw_gpu_b = get_hw_balance(dut, user_b)

        model_usdc_a = model.balances[user_a][0]
        model_gpu_a = model.balances[user_a][1]
        model_usdc_b = model.balances[user_b][0]
        model_gpu_b = model.balances[user_b][1]

        # Check for mismatches
        if hw_usdc_a != model_usdc_a or hw_gpu_a != model_gpu_a:
            dut._log.error(f"TX {tx_num}: USER A DIVERGENCE DETECTED!")
            dut._log.error(f"  User {user_a} USDC: HW={hw_usdc_a} Model={model_usdc_a} (diff={hw_usdc_a - model_usdc_a})")
            dut._log.error(f"  User {user_a} GPU:  HW={hw_gpu_a} Model={model_gpu_a} (diff={hw_gpu_a - model_gpu_a})")
            divergence_found = True
            divergence_tx = tx_num
            break

        if hw_usdc_b != model_usdc_b or hw_gpu_b != model_gpu_b:
            dut._log.error(f"TX {tx_num}: USER B DIVERGENCE DETECTED!")
            dut._log.error(f"  User {user_b} USDC: HW={hw_usdc_b} Model={model_usdc_b} (diff={hw_usdc_b - model_usdc_b})")
            dut._log.error(f"  User {user_b} GPU:  HW={hw_gpu_b} Model={model_gpu_b} (diff={hw_gpu_b - model_gpu_b})")
            divergence_found = True
            divergence_tx = tx_num
            break

        # Update history for hazard generation
        last_users.append(user_a)
        last_users.append(user_b)
        if len(last_users) > 10:
            last_users = last_users[-10:]

        # Progress reporting
        if tx_num % 1000 == 0 and tx_num > 0:
            dut._log.info(f"  TX {tx_num}: All checks passed (Conservation: USDC={hw_total_usdc}, GPU={hw_total_gpu})")

    # Report results
    if divergence_found:
        dut._log.error("=" * 80)
        dut._log.error("DIVERGENCE FOUND!")
        dut._log.error("=" * 80)
        dut._log.error(f"First divergence at transaction #{divergence_tx}")

        # Show the diverging transaction
        tx = tx_history[divergence_tx]
        dut._log.error(f"")
        dut._log.error(f"DIVERGING TRANSACTION:")
        dut._log.error(f"  Operation: {tx['op']}")
        dut._log.error(f"  User A: {tx['user_a']}")
        dut._log.error(f"  User B: {tx['user_b']}")
        dut._log.error(f"  Amount 0: {tx['amt0']}")
        dut._log.error(f"  Amount 1: {tx['amt1']}")
        dut._log.error(f"  Success: {tx['success']}")

        # Show previous 5 transactions for context
        dut._log.error(f"")
        dut._log.error(f"PREVIOUS 5 TRANSACTIONS (for context):")
        start = max(0, divergence_tx - 5)
        for i in range(start, divergence_tx):
            tx = tx_history[i]
            dut._log.error(f"  TX {tx['num']}: {tx['op']} (User {tx['user_a']} <-> User {tx['user_b']}, Amt0={tx['amt0']}, Amt1={tx['amt1']})")

        # Show vault state
        hw_vault_usdc = int(dut.m_vault_usdc.value)
        hw_vault_gpu = int(dut.m_vault_gpu.value)
        dut._log.error(f"")
        dut._log.error(f"VAULT STATE:")
        dut._log.error(f"  HW USDC: {hw_vault_usdc}, Model USDC: {model.vault[0]} (diff={hw_vault_usdc - model.vault[0]})")
        dut._log.error(f"  HW GPU:  {hw_vault_gpu}, Model GPU: {model.vault[1]} (diff={hw_vault_gpu - model.vault[1]})")

        dut._log.error("=" * 80)

        assert False, f"Divergence found at transaction {divergence_tx}"
    else:
        dut._log.info("=" * 80)
        dut._log.info(f"✅ SUCCESS: All {MAX_TXS} transactions verified!")
        dut._log.info(f"  No divergence detected")
        dut._log.info(f"  Conservation maintained throughout")
        dut._log.info("=" * 80)

@cocotb.test()
async def test_minimal_reproduction(dut):
    """
    Once divergence point is found, this test creates a minimal
    reproduction case with just the essential transactions
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== MINIMAL REPRODUCTION (Update with exact failing sequence) ===")

    # TODO: After finding divergence point, manually update this test
    # with the exact sequence of transactions that triggers the bug

    # Placeholder: This will be updated once we know the pattern
    dut._log.info("Placeholder test - update with minimal failing case once found")
    dut._log.info("✅ Test skipped (waiting for divergence identification)")
