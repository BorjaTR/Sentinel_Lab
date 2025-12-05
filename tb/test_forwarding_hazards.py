"""
Comprehensive Forwarding Hazard Verification Suite

Tests all critical hazard patterns to ensure 128-bit multi-asset
forwarding works correctly for atomic swaps.
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

    assert hw_usdc == model.balances[user_id][0], \
        f"{test_name} FAIL: User {user_id} USDC mismatch! HW:{hw_usdc} Model:{model.balances[user_id][0]}"
    assert hw_gpu == model.balances[user_id][1], \
        f"{test_name} FAIL: User {user_id} GPU mismatch! HW:{hw_gpu} Model:{model.balances[user_id][1]}"

@cocotb.test()
async def test_back_to_back_swap_same_user(dut):
    """
    Critical Test: User A swaps with B, then immediately swaps with C
    Tests if A's updated portfolio (both USDC and GPU) forwards correctly
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== TEST: Back-to-Back Swap on Same User ===")

    # TX1: User 0 swaps with User 1
    # 0 gives 10K USDC, gets 5K GPU
    # 1 gives 5K GPU, gets 10K USDC
    dut.s_opcode.value = 1  # SWAP
    dut.s_user_a.value = 0
    dut.s_user_b.value = 1
    dut.s_amount_0.value = 10000
    dut.s_amount_1.value = 5000
    dut.s_valid.value = 1
    model.process(1, 0, 1, 10000, 5000)
    await RisingEdge(dut.clk)

    # TX2: User 0 IMMEDIATELY swaps with User 2 (HAZARD!)
    # 0 gives 8K USDC, gets 3K GPU
    # CRITICAL: Must use forwarded balance from TX1, not stale RAM
    dut.s_opcode.value = 1  # SWAP
    dut.s_user_a.value = 0  # Same user A → HAZARD
    dut.s_user_b.value = 2
    dut.s_amount_0.value = 8000
    dut.s_amount_1.value = 3000
    dut.s_valid.value = 1
    model.process(1, 0, 2, 8000, 3000)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify all three users
    await verify_balance(dut, model, 0, "Back-to-back User 0")
    await verify_balance(dut, model, 1, "Back-to-back User 1")
    await verify_balance(dut, model, 2, "Back-to-back User 2")

    dut._log.info("✅ PASS: Back-to-back swap forwarding correct!")

@cocotb.test()
async def test_swap_chain_abc(dut):
    """
    Advanced Test: Three-way swap chain
    TX1: A↔B, TX2: B↔C, TX3: C↔A
    Every user is a hazard in subsequent transaction
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== TEST: Swap Chain A↔B → B↔C → C↔A ===")

    users = [10, 11, 12]  # A, B, C

    # TX1: A↔B
    dut.s_opcode.value = 1
    dut.s_user_a.value = users[0]
    dut.s_user_b.value = users[1]
    dut.s_amount_0.value = 15000
    dut.s_amount_1.value = 7000
    dut.s_valid.value = 1
    model.process(1, users[0], users[1], 15000, 7000)
    await RisingEdge(dut.clk)

    # TX2: B↔C (B is hazard from TX1)
    dut.s_opcode.value = 1
    dut.s_user_a.value = users[1]  # B was in TX1 → HAZARD
    dut.s_user_b.value = users[2]
    dut.s_amount_0.value = 12000
    dut.s_amount_1.value = 6000
    dut.s_valid.value = 1
    model.process(1, users[1], users[2], 12000, 6000)
    await RisingEdge(dut.clk)

    # TX3: C↔A (C is hazard from TX2, A is hazard from TX1)
    dut.s_opcode.value = 1
    dut.s_user_a.value = users[2]  # C was in TX2 → HAZARD
    dut.s_user_b.value = users[0]  # A was in TX1 → HAZARD (2 cycles ago)
    dut.s_amount_0.value = 9000
    dut.s_amount_1.value = 4000
    dut.s_valid.value = 1
    model.process(1, users[2], users[0], 9000, 4000)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify all three users in the chain
    for i, user in enumerate(users):
        await verify_balance(dut, model, user, f"Chain user {chr(65+i)}")

    dut._log.info("✅ PASS: Swap chain forwarding correct!")

@cocotb.test()
async def test_interleaved_swaps(dut):
    """
    Stress Test: Interleaved swap pattern
    TX1: A↔B, TX2: C↔D (no hazard), TX3: A↔C (hazard from TX1)
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== TEST: Interleaved Swaps ===")

    # TX1: 20↔21
    dut.s_opcode.value = 1
    dut.s_user_a.value = 20
    dut.s_user_b.value = 21
    dut.s_amount_0.value = 5000
    dut.s_amount_1.value = 2500
    dut.s_valid.value = 1
    model.process(1, 20, 21, 5000, 2500)
    await RisingEdge(dut.clk)

    # TX2: 22↔23 (no hazard)
    dut.s_opcode.value = 1
    dut.s_user_a.value = 22
    dut.s_user_b.value = 23
    dut.s_amount_0.value = 6000
    dut.s_amount_1.value = 3000
    dut.s_valid.value = 1
    model.process(1, 22, 23, 6000, 3000)
    await RisingEdge(dut.clk)

    # TX3: 20↔22 (20 hazard from TX1, 22 hazard from TX2)
    dut.s_opcode.value = 1
    dut.s_user_a.value = 20
    dut.s_user_b.value = 22
    dut.s_amount_0.value = 4000
    dut.s_amount_1.value = 2000
    dut.s_valid.value = 1
    model.process(1, 20, 22, 4000, 2000)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify all four users
    for user in [20, 21, 22, 23]:
        await verify_balance(dut, model, user, f"Interleaved user {user}")

    dut._log.info("✅ PASS: Interleaved swaps forwarding correct!")

@cocotb.test()
async def test_transfer_then_swap_hazard(dut):
    """
    Mixed Operation Test: Transfer followed by swap on same user
    Ensures forwarding works across different operation types
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== TEST: Transfer → Swap Hazard ===")

    # TX1: User 30 transfers USDC to User 31
    dut.s_opcode.value = 0  # TRANSFER
    dut.s_user_a.value = 30
    dut.s_user_b.value = 31
    dut.s_amount_0.value = 20000
    dut.s_amount_1.value = 0  # Not used in transfer
    dut.s_valid.value = 1
    model.process(0, 30, 31, 20000, 0)
    await RisingEdge(dut.clk)

    # TX2: User 30 IMMEDIATELY swaps with User 32
    # Must forward updated USDC from TX1 (reduced) AND GPU (unchanged)
    dut.s_opcode.value = 1  # SWAP
    dut.s_user_a.value = 30  # HAZARD
    dut.s_user_b.value = 32
    dut.s_amount_0.value = 10000
    dut.s_amount_1.value = 5000
    dut.s_valid.value = 1
    model.process(1, 30, 32, 10000, 5000)
    await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)

    # Verify
    await verify_balance(dut, model, 30, "Transfer→Swap user 30")
    await verify_balance(dut, model, 31, "Transfer→Swap user 31")
    await verify_balance(dut, model, 32, "Transfer→Swap user 32")

    dut._log.info("✅ PASS: Mixed operation forwarding correct!")

@cocotb.test()
async def test_random_hazard_stress(dut):
    """
    Stress Test: 1000 random transactions with 50% hazard rate
    Aggressive test to find any edge cases
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== TEST: Random Hazard Stress (1000 TXs) ===")

    NUM_USERS = 50  # Use subset for higher collision rate
    last_users = []
    errors = 0

    for i in range(1000):
        # 50% chance to create a hazard
        if len(last_users) > 0 and random.random() < 0.5:
            user_a = random.choice(last_users)
        else:
            user_a = random.randint(0, NUM_USERS-1)

        user_b = random.randint(0, NUM_USERS-1)
        if user_a == user_b:
            user_b = (user_b + 1) % NUM_USERS

        opcode = random.randint(0, 1)
        amt0 = random.randint(1000, 5000)
        amt1 = random.randint(1000, 3000)

        dut.s_opcode.value = opcode
        dut.s_user_a.value = user_a
        dut.s_user_b.value = user_b
        dut.s_amount_0.value = amt0
        dut.s_amount_1.value = amt1
        dut.s_valid.value = 1

        model.process(opcode, user_a, user_b, amt0, amt1)
        await RisingEdge(dut.clk)

        # Track recent users for hazard generation
        last_users.append(user_a)
        last_users.append(user_b)
        if len(last_users) > 10:
            last_users = last_users[-10:]

        if i % 200 == 0:
            dut._log.info(f"   ... {i} transactions processed ...")

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    # Verify all active users
    dut._log.info(f"Verifying {NUM_USERS} users...")
    for user in range(NUM_USERS):
        try:
            await verify_balance(dut, model, user, f"Stress test user {user}")
        except AssertionError as e:
            dut._log.error(str(e))
            errors += 1

    assert errors == 0, f"Random stress test found {errors} mismatches!"
    dut._log.info("✅ PASS: 1000 random transactions with hazards verified!")
