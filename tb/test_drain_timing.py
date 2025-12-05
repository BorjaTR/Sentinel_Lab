"""
Pipeline Drain Timing Test

Tests if balance divergence is caused by insufficient pipeline drain time.
Compares verification with 10 vs 50 cycle drain periods.
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

async def verify_balance(dut, model, user_id, test_name):
    """Compare HW vs Model for a specific user"""
    raw = int(dut.portfolios[user_id].value)
    hw_usdc = raw & 0xFFFFFFFFFFFFFFFF
    hw_gpu = (raw >> 64) & 0xFFFFFFFFFFFFFFFF

    if hw_usdc != model.balances[user_id][0]:
        return f"User {user_id} USDC: HW={hw_usdc} Model={model.balances[user_id][0]} (diff={hw_usdc - model.balances[user_id][0]})"
    if hw_gpu != model.balances[user_id][1]:
        return f"User {user_id} GPU: HW={hw_gpu} Model={model.balances[user_id][1]} (diff={hw_gpu - model.balances[user_id][1]})"
    return None

@cocotb.test()
async def test_short_drain_10_cycles(dut):
    """
    Test with SHORT drain (10 cycles) - should replicate failure
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== TEST: Short Drain (10 cycles) - High Hazard Density ===")

    # Generate 2000 transactions with 50% hazard rate (aggressive)
    random.seed(42)  # Fixed seed for reproducibility
    NUM_USERS = 50
    last_users = []
    transactions = []

    for _ in range(2000):
        if len(last_users) > 0 and random.random() < 0.5:
            user_a = random.choice(last_users)  # Create hazard
        else:
            user_a = random.randint(0, NUM_USERS - 1)

        user_b = random.randint(0, NUM_USERS - 1)
        while user_b == user_a:
            user_b = random.randint(0, NUM_USERS - 1)

        transactions.append((random.randint(0, 1), user_a, user_b,
                           random.randint(1000, 5000), random.randint(1000, 3000)))

        last_users.append(user_a)
        last_users.append(user_b)
        if len(last_users) > 10:
            last_users = last_users[-10:]

    # Execute all transactions
    for op, u_a, u_b, amt0, amt1 in transactions:
        dut.s_opcode.value = op
        dut.s_user_a.value = u_a
        dut.s_user_b.value = u_b
        dut.s_amount_0.value = amt0
        dut.s_amount_1.value = amt1
        dut.s_valid.value = 1
        model.process(op, u_a, u_b, amt0, amt1)
        await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    # SHORT DRAIN: Only 10 cycles
    for _ in range(10):
        await RisingEdge(dut.clk)

    # Verify
    errors = []
    for user in range(NUM_USERS):
        err = await verify_balance(dut, model, user, "Short drain")
        if err:
            errors.append(err)

    if len(errors) > 0:
        dut._log.warning(f"SHORT DRAIN: Found {len(errors)} mismatches")
        for err in errors[:5]:  # Show first 5
            dut._log.warning(f"  {err}")
    else:
        dut._log.info("SHORT DRAIN: No mismatches found!")

    # Don't assert - just report
    dut._log.info(f"Result: {len(errors)} errors with 10-cycle drain")

@cocotb.test()
async def test_long_drain_50_cycles(dut):
    """
    Test with LONG drain (50 cycles) - hypothesis: should fix issue
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== TEST: Long Drain (50 cycles) - Same Pattern ===")

    # EXACT SAME TRANSACTIONS as short drain test
    random.seed(42)  # Same seed!
    NUM_USERS = 50
    last_users = []
    transactions = []

    for _ in range(2000):
        if len(last_users) > 0 and random.random() < 0.5:
            user_a = random.choice(last_users)
        else:
            user_a = random.randint(0, NUM_USERS - 1)

        user_b = random.randint(0, NUM_USERS - 1)
        while user_b == user_a:
            user_b = random.randint(0, NUM_USERS - 1)

        transactions.append((random.randint(0, 1), user_a, user_b,
                           random.randint(1000, 5000), random.randint(1000, 3000)))

        last_users.append(user_a)
        last_users.append(user_b)
        if len(last_users) > 10:
            last_users = last_users[-10:]

    # Execute all transactions
    for op, u_a, u_b, amt0, amt1 in transactions:
        dut.s_opcode.value = op
        dut.s_user_a.value = u_a
        dut.s_user_b.value = u_b
        dut.s_amount_0.value = amt0
        dut.s_amount_1.value = amt1
        dut.s_valid.value = 1
        model.process(op, u_a, u_b, amt0, amt1)
        await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    # LONG DRAIN: 50 cycles to ensure full pipeline flush
    for _ in range(50):
        await RisingEdge(dut.clk)

    # Verify
    errors = []
    for user in range(NUM_USERS):
        err = await verify_balance(dut, model, user, "Long drain")
        if err:
            errors.append(err)

    if len(errors) > 0:
        dut._log.error(f"LONG DRAIN: Still found {len(errors)} mismatches")
        for err in errors[:5]:
            dut._log.error(f"  {err}")
        assert False, f"Long drain did not fix issue - {len(errors)} errors remain"
    else:
        dut._log.info("✅ LONG DRAIN: No mismatches! Pipeline timing was the issue!")

@cocotb.test()
async def test_incremental_drain_search(dut):
    """
    Binary search for minimum drain cycles needed
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())

    dut._log.info("=== TEST: Incremental Drain Cycle Search ===")

    for drain_cycles in [5, 10, 15, 20, 25, 30]:
        model = ExchangeModel()

        dut.rst_n.value = 0
        await RisingEdge(dut.clk)
        dut.rst_n.value = 1
        dut.s_valid.value = 0
        await RisingEdge(dut.clk)

        # Same pattern
        random.seed(42)
        NUM_USERS = 50
        last_users = []

        for _ in range(2000):
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

            dut.s_opcode.value = op
            dut.s_user_a.value = user_a
            dut.s_user_b.value = user_b
            dut.s_amount_0.value = amt0
            dut.s_amount_1.value = amt1
            dut.s_valid.value = 1
            model.process(op, user_a, user_b, amt0, amt1)
            await RisingEdge(dut.clk)

            last_users.append(user_a)
            last_users.append(user_b)
            if len(last_users) > 10:
                last_users = last_users[-10:]

        dut.s_valid.value = 0
        for _ in range(drain_cycles):
            await RisingEdge(dut.clk)

        # Verify
        errors = 0
        for user in range(NUM_USERS):
            err = await verify_balance(dut, model, user, "Incremental")
            if err:
                errors += 1

        dut._log.info(f"Drain={drain_cycles} cycles: {errors} mismatches")

        if errors == 0:
            dut._log.info(f"✅ Minimum drain cycles needed: {drain_cycles}")
            break
