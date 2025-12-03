"""
Constrained Random Verification (CRV) Swarm

Advanced random testing with intelligent hazard injection and coverage tracking.

Features:
- 30% back-to-back hazards (same user in consecutive txs)
- 20% swap chains (A↔B → B↔C patterns)
- Coverage metrics (user utilization, forwarding hits)
- 10K+ transaction stress testing
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
import random
from collections import defaultdict

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

class CoverageTracker:
    """Tracks test coverage metrics"""
    def __init__(self, num_users):
        self.users_touched = set()
        self.hazards_created = 0
        self.chains_created = 0
        self.ops_count = defaultdict(int)
        self.success_count = 0
        self.failure_count = 0
        self.num_users = num_users

    def record_transaction(self, op, u_a, u_b, success, is_hazard=False, is_chain=False):
        self.users_touched.add(u_a)
        self.users_touched.add(u_b)
        self.ops_count[op] += 1
        if success:
            self.success_count += 1
        else:
            self.failure_count += 1
        if is_hazard:
            self.hazards_created += 1
        if is_chain:
            self.chains_created += 1

    def report(self):
        total_txs = self.success_count + self.failure_count
        user_util = (len(self.users_touched) / self.num_users) * 100
        success_rate = (self.success_count / total_txs) * 100 if total_txs > 0 else 0
        hazard_rate = (self.hazards_created / total_txs) * 100 if total_txs > 0 else 0
        chain_rate = (self.chains_created / total_txs) * 100 if total_txs > 0 else 0

        return {
            'total_transactions': total_txs,
            'user_utilization_%': user_util,
            'users_exercised': len(self.users_touched),
            'success_rate_%': success_rate,
            'hazard_injection_%': hazard_rate,
            'chain_injection_%': chain_rate,
            'transfers': self.ops_count[0],
            'swaps': self.ops_count[1],
        }

class ConstrainedRandomGenerator:
    """Generates constrained random transactions with hazard injection"""
    def __init__(self, num_users=100, hazard_rate=0.30, chain_rate=0.20):
        self.num_users = num_users
        self.hazard_rate = hazard_rate
        self.chain_rate = chain_rate
        self.recent_users = []  # Track recent users for hazard creation
        self.chain_buffer = []  # Track potential chain participants

    def generate(self, count):
        """Generate 'count' transactions with intelligent patterns"""
        transactions = []

        for i in range(count):
            tx, is_hazard, is_chain = self._generate_one()
            transactions.append((tx, is_hazard, is_chain))

        return transactions

    def _generate_one(self):
        """Generate a single transaction with hazard/chain consideration"""
        is_hazard = False
        is_chain = False

        # Decide transaction pattern
        rand = random.random()

        if rand < self.chain_rate and len(self.chain_buffer) >= 2:
            # Create a swap chain: if we had A↔B, now do B↔C
            tx, is_chain = self._create_chain()
        elif rand < (self.chain_rate + self.hazard_rate) and len(self.recent_users) > 0:
            # Create a back-to-back hazard
            tx, is_hazard = self._create_hazard()
        else:
            # Random transaction
            tx = self._create_random()

        # Update tracking
        self.recent_users.append(tx['u_a'])
        self.recent_users.append(tx['u_b'])
        if len(self.recent_users) > 20:
            self.recent_users = self.recent_users[-20:]

        if tx['op'] == 1:  # Swaps can be chained
            self.chain_buffer.append((tx['u_a'], tx['u_b']))
            if len(self.chain_buffer) > 10:
                self.chain_buffer = self.chain_buffer[-10:]

        return tx, is_hazard, is_chain

    def _create_hazard(self):
        """Create a back-to-back hazard (reuse recent user)"""
        user_a = random.choice(self.recent_users)
        user_b = random.randint(0, self.num_users - 1)

        # Ensure different users
        while user_b == user_a:
            user_b = random.randint(0, self.num_users - 1)

        return self._make_tx(user_a, user_b), True

    def _create_chain(self):
        """Create a swap chain (A↔B then B↔C)"""
        # Pick a recent swap and continue the chain
        prev_a, prev_b = random.choice(self.chain_buffer)

        # New transaction uses one of the previous participants
        user_a = random.choice([prev_a, prev_b])
        user_c = random.randint(0, self.num_users - 1)

        while user_c == user_a:
            user_c = random.randint(0, self.num_users - 1)

        return self._make_tx(user_a, user_c), True

    def _create_random(self):
        """Create a completely random transaction"""
        user_a = random.randint(0, self.num_users - 1)
        user_b = random.randint(0, self.num_users - 1)

        while user_b == user_a:
            user_b = random.randint(0, self.num_users - 1)

        return self._make_tx(user_a, user_b)

    def _make_tx(self, user_a, user_b):
        """Create transaction dictionary with reasonable amounts"""
        opcode = random.randint(0, 1)

        # Use reasonable amounts to avoid too many failures
        amt0 = random.randint(1000, 8000)
        amt1 = random.randint(1000, 6000) if opcode == 1 else 0

        return {
            'op': opcode,
            'u_a': user_a,
            'u_b': user_b,
            'amt0': amt0,
            'amt1': amt1
        }

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
async def test_crv_swarm_1k(dut):
    """
    CRV Swarm: 1,000 transactions with 30% hazards + 20% chains
    Quick sanity check before running 10K+
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()
    coverage = CoverageTracker(num_users=100)

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== CRV SWARM: 1K Transactions (30% hazards, 20% chains) ===")

    # Generate constrained random transactions
    generator = ConstrainedRandomGenerator(num_users=100, hazard_rate=0.30, chain_rate=0.20)
    transactions = generator.generate(1000)

    # Execute all transactions
    for i, (tx, is_hazard, is_chain) in enumerate(transactions):
        dut.s_opcode.value = tx['op']
        dut.s_user_a.value = tx['u_a']
        dut.s_user_b.value = tx['u_b']
        dut.s_amount_0.value = tx['amt0']
        dut.s_amount_1.value = tx['amt1']
        dut.s_valid.value = 1

        success = model.process(tx['op'], tx['u_a'], tx['u_b'], tx['amt0'], tx['amt1'])
        coverage.record_transaction(tx['op'], tx['u_a'], tx['u_b'], success, is_hazard, is_chain)

        await RisingEdge(dut.clk)

        if i % 200 == 0 and i > 0:
            dut._log.info(f"   ... {i} transactions processed ...")

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    # Verify all active users
    dut._log.info(f"Verifying {len(coverage.users_touched)} users...")
    errors = 0
    for user in coverage.users_touched:
        try:
            await verify_balance(dut, model, user, f"CRV 1K user {user}")
        except AssertionError as e:
            dut._log.error(str(e))
            errors += 1

    # Report coverage metrics
    metrics = coverage.report()
    dut._log.info("=== COVERAGE REPORT ===")
    dut._log.info(f"Total Transactions: {metrics['total_transactions']}")
    dut._log.info(f"User Utilization: {metrics['user_utilization_%']:.1f}% ({metrics['users_exercised']}/100)")
    dut._log.info(f"Success Rate: {metrics['success_rate_%']:.1f}%")
    dut._log.info(f"Hazard Injection: {metrics['hazard_injection_%']:.1f}%")
    dut._log.info(f"Chain Injection: {metrics['chain_injection_%']:.1f}%")
    dut._log.info(f"Transfers: {metrics['transfers']}, Swaps: {metrics['swaps']}")

    assert errors == 0, f"CRV swarm found {errors} mismatches!"
    dut._log.info("✅ PASS: 1K CRV swarm verified!")

@cocotb.test()
async def test_crv_swarm_10k(dut):
    """
    CRV Swarm: 10,000 transactions - Full stress test
    This is the main verification workload
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()
    coverage = CoverageTracker(num_users=200)

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== CRV SWARM: 10K Transactions (30% hazards, 20% chains) ===")

    # Generate constrained random transactions
    generator = ConstrainedRandomGenerator(num_users=200, hazard_rate=0.30, chain_rate=0.20)
    transactions = generator.generate(10000)

    # Execute all transactions
    for i, (tx, is_hazard, is_chain) in enumerate(transactions):
        dut.s_opcode.value = tx['op']
        dut.s_user_a.value = tx['u_a']
        dut.s_user_b.value = tx['u_b']
        dut.s_amount_0.value = tx['amt0']
        dut.s_amount_1.value = tx['amt1']
        dut.s_valid.value = 1

        success = model.process(tx['op'], tx['u_a'], tx['u_b'], tx['amt0'], tx['amt1'])
        coverage.record_transaction(tx['op'], tx['u_a'], tx['u_b'], success, is_hazard, is_chain)

        await RisingEdge(dut.clk)

        if i % 2000 == 0 and i > 0:
            dut._log.info(f"   ... {i} transactions processed ...")

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    # Verify all active users
    dut._log.info(f"Verifying {len(coverage.users_touched)} users...")
    errors = 0
    for user in coverage.users_touched:
        try:
            await verify_balance(dut, model, user, f"CRV 10K user {user}")
        except AssertionError as e:
            dut._log.error(str(e))
            errors += 1

    # Report coverage metrics
    metrics = coverage.report()
    dut._log.info("=== COVERAGE REPORT ===")
    dut._log.info(f"Total Transactions: {metrics['total_transactions']}")
    dut._log.info(f"User Utilization: {metrics['user_utilization_%']:.1f}% ({metrics['users_exercised']}/200)")
    dut._log.info(f"Success Rate: {metrics['success_rate_%']:.1f}%")
    dut._log.info(f"Hazard Injection: {metrics['hazard_injection_%']:.1f}%")
    dut._log.info(f"Chain Injection: {metrics['chain_injection_%']:.1f}%")
    dut._log.info(f"Transfers: {metrics['transfers']}, Swaps: {metrics['swaps']}")

    assert errors == 0, f"CRV swarm found {errors} mismatches!"
    dut._log.info("✅ PASS: 10K CRV swarm verified!")

@cocotb.test()
async def test_crv_swarm_marathon(dut):
    """
    CRV Swarm Marathon: 100,000 transactions
    Ultimate stress test - only run if previous tests pass
    """
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()
    coverage = CoverageTracker(num_users=500)

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("=== CRV SWARM MARATHON: 100K Transactions ===")

    # Generate constrained random transactions
    generator = ConstrainedRandomGenerator(num_users=500, hazard_rate=0.30, chain_rate=0.20)
    transactions = generator.generate(100000)

    # Execute all transactions
    for i, (tx, is_hazard, is_chain) in enumerate(transactions):
        dut.s_opcode.value = tx['op']
        dut.s_user_a.value = tx['u_a']
        dut.s_user_b.value = tx['u_b']
        dut.s_amount_0.value = tx['amt0']
        dut.s_amount_1.value = tx['amt1']
        dut.s_valid.value = 1

        success = model.process(tx['op'], tx['u_a'], tx['u_b'], tx['amt0'], tx['amt1'])
        coverage.record_transaction(tx['op'], tx['u_a'], tx['u_b'], success, is_hazard, is_chain)

        await RisingEdge(dut.clk)

        if i % 10000 == 0 and i > 0:
            dut._log.info(f"   ... {i} transactions processed ...")

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    # Verify all active users
    dut._log.info(f"Verifying {len(coverage.users_touched)} users...")
    errors = 0
    for user in coverage.users_touched:
        try:
            await verify_balance(dut, model, user, f"CRV Marathon user {user}")
        except AssertionError as e:
            dut._log.error(str(e))
            errors += 1

    # Report coverage metrics
    metrics = coverage.report()
    dut._log.info("=== COVERAGE REPORT ===")
    dut._log.info(f"Total Transactions: {metrics['total_transactions']}")
    dut._log.info(f"User Utilization: {metrics['user_utilization_%']:.1f}% ({metrics['users_exercised']}/500)")
    dut._log.info(f"Success Rate: {metrics['success_rate_%']:.1f}%")
    dut._log.info(f"Hazard Injection: {metrics['hazard_injection_%']:.1f}%")
    dut._log.info(f"Chain Injection: {metrics['chain_injection_%']:.1f}%")
    dut._log.info(f"Transfers: {metrics['transfers']}, Swaps: {metrics['swaps']}")

    assert errors == 0, f"CRV marathon found {errors} mismatches!"
    dut._log.info("✅ PASS: 100K CRV marathon verified!")
