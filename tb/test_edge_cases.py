"""
Directed Edge-Case Test Suite

Targets specific boundary conditions and corner cases that might expose bugs:
- Self-swaps (A↔A should be no-op)
- Exact balance transfers (drain to zero)
- Insufficient funds scenarios
- Overflow boundaries
- Zero amount transactions
- Maximum value transactions
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

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

async def verify_balance(dut, model, user_id, test_name):
    """Compare HW vs Model for a specific user"""
    raw = int(dut.portfolios[user_id].value)
    hw_usdc = raw & 0xFFFFFFFFFFFFFFFF
    hw_gpu = (raw >> 64) & 0xFFFFFFFFFFFFFFFF

    assert hw_usdc == model.balances[user_id][0], \
        f"{test_name} FAIL: User {user_id} USDC mismatch! HW:{hw_usdc} Model:{model.balances[user_id][0]}"
    assert hw_gpu == model.balances[user_id][1], \
        f"{test_name} FAIL: User {user_id} GPU mismatch! HW:{hw_gpu} Model:{model.balances[user_id][1]}"

@cocotb.test()
async def test_self_swap(dut):
    """
    Edge Case: Self-swap (A swaps with A)
    Expected: Should succeed but be a no-op (no balance changes)
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Self-Swap (A↔A) ===")

    # User 10 tries to swap with itself
    dut.s_opcode.value = 1  # SWAP
    dut.s_user_a.value = 10
    dut.s_user_b.value = 10  # Same user!
    dut.s_amount_0.value = 5000
    dut.s_amount_1.value = 3000
    dut.s_valid.value = 1
    model.process(1, 10, 10, 5000, 3000)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify balance unchanged
    await verify_balance(dut, model, 10, "Self-swap")

    # Check vault didn't collect fees (no-op means no fees)
    hw_vault_usdc = int(dut.m_vault_usdc.value)
    hw_vault_gpu = int(dut.m_vault_gpu.value)
    assert hw_vault_usdc == 0 and hw_vault_gpu == 0, "Self-swap should not collect fees"

    dut._log.info("✅ PASS: Self-swap behaves as no-op")

@cocotb.test()
async def test_exact_balance_drain(dut):
    """
    Edge Case: Transfer exact balance (including fee) to drain to zero
    Tests if hardware correctly handles balance going to exactly 0
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Exact Balance Drain to Zero ===")

    # User 20 starts with 1M USDC
    # Transfer 999,512 USDC (leaves exactly 488 for fee, so 999512+488=1000000)
    fee = 999512 >> 11  # fee = 488
    amount = 999512

    dut._log.info(f"Draining 1M USDC: transfer={amount}, fee={fee}, total={amount+fee}")

    dut.s_opcode.value = 0  # TRANSFER
    dut.s_user_a.value = 20
    dut.s_user_b.value = 21
    dut.s_amount_0.value = amount
    dut.s_amount_1.value = 0
    dut.s_valid.value = 1
    model.process(0, 20, 21, amount, 0)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify User 20 has exactly 0 USDC
    await verify_balance(dut, model, 20, "Drain sender")
    await verify_balance(dut, model, 21, "Drain receiver")

    raw = int(dut.portfolios[20].value)
    hw_usdc = raw & 0xFFFFFFFFFFFFFFFF
    assert hw_usdc == 0, f"User 20 should have 0 USDC, has {hw_usdc}"

    dut._log.info("✅ PASS: Exact balance drain to zero works")

@cocotb.test()
async def test_insufficient_funds_transfer(dut):
    """
    Edge Case: Attempt transfer with insufficient funds
    Expected: Transaction should fail, no state change
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Insufficient Funds Transfer ===")

    # Attempt to transfer more than balance
    dut.s_opcode.value = 0  # TRANSFER
    dut.s_user_a.value = 30
    dut.s_user_b.value = 31
    dut.s_amount_0.value = 2000000  # More than 1M balance
    dut.s_amount_1.value = 0
    dut.s_valid.value = 1
    model.process(0, 30, 31, 2000000, 0)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify balances unchanged
    await verify_balance(dut, model, 30, "Insufficient funds sender")
    await verify_balance(dut, model, 31, "Insufficient funds receiver")

    dut._log.info("✅ PASS: Insufficient funds correctly rejected")

@cocotb.test()
async def test_insufficient_funds_swap(dut):
    """
    Edge Case: Attempt swap where one party has insufficient funds
    Expected: Transaction should fail atomically, no partial update
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Insufficient Funds Swap (Atomic Failure) ===")

    # User 40 tries to swap but doesn't have enough USDC
    dut.s_opcode.value = 1  # SWAP
    dut.s_user_a.value = 40
    dut.s_user_b.value = 41
    dut.s_amount_0.value = 2000000  # More than balance
    dut.s_amount_1.value = 5000
    dut.s_valid.value = 1
    model.process(1, 40, 41, 2000000, 5000)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify BOTH users unchanged (atomicity)
    await verify_balance(dut, model, 40, "Atomic failure user A")
    await verify_balance(dut, model, 41, "Atomic failure user B")

    dut._log.info("✅ PASS: Atomic swap failure preserves both balances")

@cocotb.test()
async def test_zero_amount_transfer(dut):
    """
    Edge Case: Transfer zero amount
    Expected: Should succeed (fee still charged) or be rejected
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Zero Amount Transfer ===")

    dut.s_opcode.value = 0  # TRANSFER
    dut.s_user_a.value = 50
    dut.s_user_b.value = 51
    dut.s_amount_0.value = 0  # Zero transfer
    dut.s_amount_1.value = 0
    dut.s_valid.value = 1
    model.process(0, 50, 51, 0, 0)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    await verify_balance(dut, model, 50, "Zero transfer sender")
    await verify_balance(dut, model, 51, "Zero transfer receiver")

    dut._log.info("✅ PASS: Zero amount transfer handled")

@cocotb.test()
async def test_maximum_value_transfer(dut):
    """
    Edge Case: Transfer near maximum 64-bit value (overflow boundary)
    Expected: Should work if balance sufficient, or reject properly
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Maximum Value Transfer ===")

    # Try to transfer near max value (will fail due to insufficient funds, but tests overflow handling)
    MAX_VAL = (1 << 63) - 1  # Close to max 64-bit signed

    dut.s_opcode.value = 0  # TRANSFER
    dut.s_user_a.value = 60
    dut.s_user_b.value = 61
    dut.s_amount_0.value = MAX_VAL
    dut.s_amount_1.value = 0
    dut.s_valid.value = 1
    model.process(0, 60, 61, MAX_VAL, 0)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Should reject (insufficient funds), but shouldn't overflow
    await verify_balance(dut, model, 60, "Max value sender")
    await verify_balance(dut, model, 61, "Max value receiver")

    dut._log.info("✅ PASS: Maximum value handled without overflow")

@cocotb.test()
async def test_rapid_fire_same_user(dut):
    """
    Edge Case: Same user in 10 consecutive transactions
    Extreme hazard density to stress forwarding logic
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Rapid-Fire Same User (10x consecutive) ===")

    # User 70 does 10 swaps in a row with different partners
    for i in range(10):
        partner = 71 + i
        dut.s_opcode.value = 1  # SWAP
        dut.s_user_a.value = 70  # Same user every time
        dut.s_user_b.value = partner
        dut.s_amount_0.value = 1000 + (i * 100)
        dut.s_amount_1.value = 500 + (i * 50)
        dut.s_valid.value = 1
        model.process(1, 70, partner, 1000 + (i * 100), 500 + (i * 50))
        await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    # Verify user 70 and all partners
    await verify_balance(dut, model, 70, "Rapid-fire main user")
    for i in range(10):
        await verify_balance(dut, model, 71 + i, f"Rapid-fire partner {i}")

    dut._log.info("✅ PASS: Rapid-fire same user (extreme hazards) works")

@cocotb.test()
async def test_ping_pong_pattern(dut):
    """
    Edge Case: Ping-pong pattern (A→B, B→A, A→B, B→A)
    Tests bidirectional hazards
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== EDGE CASE: Ping-Pong Pattern (A↔B alternating) ===")

    users = [90, 91]
    for i in range(10):
        # Alternate direction
        u_a = users[i % 2]
        u_b = users[(i + 1) % 2]

        dut.s_opcode.value = 0  # TRANSFER
        dut.s_user_a.value = u_a
        dut.s_user_b.value = u_b
        dut.s_amount_0.value = 2000 + (i * 100)
        dut.s_amount_1.value = 0
        dut.s_valid.value = 1
        model.process(0, u_a, u_b, 2000 + (i * 100), 0)
        await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    await verify_balance(dut, model, 90, "Ping-pong user A")
    await verify_balance(dut, model, 91, "Ping-pong user B")

    dut._log.info("✅ PASS: Ping-pong pattern works")
