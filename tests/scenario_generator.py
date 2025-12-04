"""
Random Scenario Generator for Comprehensive Verification

Generates random transaction sequences with configurable parameters
to stress-test all layers of Sentinel Cloud.

Coverage Axes:
- User counts: {8, 16, 64, 256, 1024}
- Opcodes: TRANSFER, SWAP, REWARD, PENALTY
- Roles: client, validator, miner, treasury
- Amount distributions: small, large, mixed
- Fee configurations: 0-10000 bps
- Time patterns: uniform, bursty, clustered
"""

import random
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
from enum import Enum

from sentinel_cloud.schema import SentinelTx, Opcode

# Define UserRole locally since it's not in schema
class UserRole:
    CLIENT = "client"
    VALIDATOR = "validator"
    MINER = "miner"
    TREASURY = "treasury"


class AmountDistribution(Enum):
    SMALL = "small"           # 1-1000
    MEDIUM = "medium"         # 1000-100000
    LARGE = "large"           # 100000-1000000
    VERY_LARGE = "very_large" # Near 2^63 boundary
    MIXED = "mixed"           # Random mix


class OpcodeDistribution(Enum):
    TRANSFER_HEAVY = "transfer_heavy"  # 80% TRANSFER
    SWAP_HEAVY = "swap_heavy"          # 80% SWAP
    REWARD_HEAVY = "reward_heavy"      # 50% REWARD, 30% TRANSFER
    BALANCED = "balanced"              # Equal distribution
    DEGENERATE = "degenerate"          # Single opcode only


class RoleDistribution(Enum):
    CLIENT_HEAVY = "client_heavy"      # 70% clients
    VALIDATOR_HEAVY = "validator_heavy"  # 70% validators
    MINER_HEAVY = "miner_heavy"        # 70% miners
    BALANCED = "balanced"              # Equal distribution
    DEGENERATE = "degenerate"          # Single role only


class TimePattern(Enum):
    UNIFORM = "uniform"        # Evenly spaced
    BURSTY = "bursty"          # Clustered in time
    SESSION_GAPS = "session_gaps"  # Large gaps between clusters
    RANDOM = "random"          # Completely random


@dataclass
class ScenarioConfig:
    """Configuration for random scenario generation"""
    num_users: int = 64
    num_transactions: int = 1000
    amount_dist: AmountDistribution = AmountDistribution.MIXED
    opcode_dist: OpcodeDistribution = OpcodeDistribution.BALANCED
    role_dist: RoleDistribution = RoleDistribution.BALANCED
    time_pattern: TimePattern = TimePattern.UNIFORM
    seed: Optional[int] = None

    # Amount range bounds
    min_amount: int = 1
    max_amount: int = 1_000_000

    # Timestamp range (seconds)
    start_time: int = 1700000000
    time_span: int = 86400  # 24 hours default

    # Hazard injection (for pipeline testing)
    hazard_probability: float = 0.0  # 0.0-1.0, chance of back-to-back same user

    # Edge case injection
    edge_case_probability: float = 0.0  # Chance of exact balance, overflow, etc.


class ScenarioGenerator:
    """Generates random transaction scenarios for verification"""

    def __init__(self, config: ScenarioConfig):
        self.config = config
        if config.seed is not None:
            random.seed(config.seed)

        # Initialize role distribution
        self.roles = self._init_role_distribution()

        # Coverage tracking
        all_opcodes = ['transfer', 'swap', 'reward', 'penalty']
        all_roles = ['client', 'validator', 'miner', 'treasury']
        self.coverage = {
            'opcodes': {op: 0 for op in all_opcodes},
            'roles': {role: 0 for role in all_roles},
            'hazards': 0,
            'edge_cases': 0,
            'amount_ranges': {'small': 0, 'medium': 0, 'large': 0, 'very_large': 0},
        }

    def _init_role_distribution(self) -> Dict[str, float]:
        """Initialize role probability distribution"""
        if self.config.role_dist == RoleDistribution.CLIENT_HEAVY:
            return {
                'client': 0.70,
                'validator': 0.15,
                'miner': 0.10,
                'treasury': 0.05,
            }
        elif self.config.role_dist == RoleDistribution.VALIDATOR_HEAVY:
            return {
                'validator': 0.70,
                'client': 0.15,
                'miner': 0.10,
                'treasury': 0.05,
            }
        elif self.config.role_dist == RoleDistribution.MINER_HEAVY:
            return {
                'miner': 0.70,
                'client': 0.15,
                'validator': 0.10,
                'treasury': 0.05,
            }
        elif self.config.role_dist == RoleDistribution.DEGENERATE:
            # All one role
            role = random.choice(['client', 'validator', 'miner', 'treasury'])
            return {r: (1.0 if r == role else 0.0) for r in ['client', 'validator', 'miner', 'treasury']}
        else:  # BALANCED
            return {'client': 0.25, 'validator': 0.25, 'miner': 0.25, 'treasury': 0.25}

    def _sample_role(self) -> str:
        """Sample a role according to distribution"""
        r = random.random()
        cumulative = 0.0
        for role, prob in self.roles.items():
            cumulative += prob
            if r <= cumulative:
                self.coverage['roles'][role] += 1
                return role
        return 'client'  # Fallback

    def _sample_opcode(self) -> str:
        """Sample an opcode according to distribution"""
        dist = self.config.opcode_dist

        if dist == OpcodeDistribution.TRANSFER_HEAVY:
            opcodes = ['transfer'] * 8 + ['swap', 'reward']
        elif dist == OpcodeDistribution.SWAP_HEAVY:
            opcodes = ['swap'] * 8 + ['transfer', 'reward']
        elif dist == OpcodeDistribution.REWARD_HEAVY:
            opcodes = ['reward'] * 5 + ['transfer'] * 3 + ['swap', 'penalty']
        elif dist == OpcodeDistribution.DEGENERATE:
            opcode = random.choice(['transfer', 'swap', 'reward', 'penalty'])
            opcodes = [opcode] * 10
        else:  # BALANCED
            opcodes = ['transfer', 'swap', 'reward', 'penalty']

        opcode = random.choice(opcodes)
        self.coverage['opcodes'][opcode] += 1
        return opcode

    def _sample_amount(self) -> int:
        """Sample an amount according to distribution"""
        dist = self.config.amount_dist

        # Inject edge cases
        if random.random() < self.config.edge_case_probability:
            self.coverage['edge_cases'] += 1
            # Edge cases: 0, 1, max-1, max
            edge = random.choice([0, 1, 2**63 - 2, 2**63 - 1])
            return min(edge, self.config.max_amount)

        if dist == AmountDistribution.SMALL:
            amount = random.randint(1, 1000)
            self.coverage['amount_ranges']['small'] += 1
        elif dist == AmountDistribution.MEDIUM:
            amount = random.randint(1000, 100_000)
            self.coverage['amount_ranges']['medium'] += 1
        elif dist == AmountDistribution.LARGE:
            amount = random.randint(100_000, 1_000_000)
            self.coverage['amount_ranges']['large'] += 1
        elif dist == AmountDistribution.VERY_LARGE:
            amount = random.randint(2**60, 2**63 - 1)
            self.coverage['amount_ranges']['very_large'] += 1
        else:  # MIXED
            # Random selection across ranges
            range_choice = random.choice(['small', 'medium', 'large', 'very_large'])
            if range_choice == 'small':
                amount = random.randint(1, 1000)
                self.coverage['amount_ranges']['small'] += 1
            elif range_choice == 'medium':
                amount = random.randint(1000, 100_000)
                self.coverage['amount_ranges']['medium'] += 1
            elif range_choice == 'large':
                amount = random.randint(100_000, 1_000_000)
                self.coverage['amount_ranges']['large'] += 1
            else:
                amount = random.randint(2**60, 2**63 - 1)
                self.coverage['amount_ranges']['very_large'] += 1

        return min(amount, self.config.max_amount)

    def _sample_timestamp(self, index: int) -> int:
        """Sample a timestamp according to time pattern"""
        pattern = self.config.time_pattern

        if pattern == TimePattern.UNIFORM:
            # Evenly spaced
            interval = self.config.time_span / self.config.num_transactions
            return self.config.start_time + int(index * interval)

        elif pattern == TimePattern.BURSTY:
            # Clustered in 10 bursts
            burst_id = index % 10
            burst_start = self.config.start_time + (burst_id * self.config.time_span // 10)
            return burst_start + random.randint(0, 100)

        elif pattern == TimePattern.SESSION_GAPS:
            # Sessions with 10-minute gaps
            session_id = index // 100
            session_start = self.config.start_time + (session_id * 600)  # 10 min gaps
            return session_start + random.randint(0, 60)

        else:  # RANDOM
            return self.config.start_time + random.randint(0, self.config.time_span)

    def _inject_hazard(self, prev_tx: Optional[SentinelTx]) -> Tuple[int, int]:
        """Inject pipeline hazards (back-to-back same users)"""
        if prev_tx and random.random() < self.config.hazard_probability:
            self.coverage['hazards'] += 1
            # Re-use one of the previous users
            if random.random() < 0.5:
                return prev_tx.user_a, random.randint(0, self.config.num_users - 1)
            else:
                return random.randint(0, self.config.num_users - 1), prev_tx.user_b

        # Normal random users
        return (
            random.randint(0, self.config.num_users - 1),
            random.randint(0, self.config.num_users - 1)
        )

    def generate(self) -> List[SentinelTx]:
        """Generate a random transaction scenario"""
        transactions = []
        prev_tx = None

        for i in range(self.config.num_transactions):
            opcode = self._sample_opcode()
            user_a, user_b = self._inject_hazard(prev_tx)
            role_a = self._sample_role()
            role_b = self._sample_role()
            timestamp = self._sample_timestamp(i)

            # Generate amounts based on opcode
            if opcode == 'transfer':
                amount0 = self._sample_amount()
                amount1 = 0
            elif opcode == 'swap':
                amount0 = self._sample_amount()
                amount1 = self._sample_amount()
            elif opcode == 'reward':
                amount0 = self._sample_amount()
                amount1 = 0
            elif opcode == 'penalty':
                amount0 = self._sample_amount()
                amount1 = 0
            else:
                amount0 = self._sample_amount()
                amount1 = 0

            tx = SentinelTx(
                timestamp=timestamp,
                user_a=user_a,
                user_b=user_b,
                asset0_amount=amount0,
                asset1_amount=amount1,
                opcode=opcode,
                role_a=role_a,
                role_b=role_b,
            )

            transactions.append(tx)
            prev_tx = tx

        # Sort by timestamp for realism
        transactions.sort(key=lambda tx: tx.timestamp)

        return transactions

    def get_coverage_report(self) -> str:
        """Generate a coverage report"""
        lines = [
            "=" * 60,
            "SCENARIO COVERAGE REPORT",
            "=" * 60,
            f"Configuration: {self.config.num_users} users, {self.config.num_transactions} txs",
            f"Seed: {self.config.seed}",
            "",
            "Opcode Coverage:",
        ]

        for opcode, count in self.coverage['opcodes'].items():
            pct = 100 * count / self.config.num_transactions
            lines.append(f"  {opcode:12s}: {count:6d} ({pct:5.1f}%)")

        lines.append("")
        lines.append("Role Coverage:")
        total_roles = sum(self.coverage['roles'].values())
        for role, count in self.coverage['roles'].items():
            pct = 100 * count / total_roles if total_roles > 0 else 0
            lines.append(f"  {role:12s}: {count:6d} ({pct:5.1f}%)")

        lines.append("")
        lines.append("Amount Range Coverage:")
        for range_name, count in self.coverage['amount_ranges'].items():
            pct = 100 * count / self.config.num_transactions
            lines.append(f"  {range_name:12s}: {count:6d} ({pct:5.1f}%)")

        lines.append("")
        lines.append(f"Pipeline Hazards Injected: {self.coverage['hazards']}")
        lines.append(f"Edge Cases Injected: {self.coverage['edge_cases']}")
        lines.append("=" * 60)

        return "\n".join(lines)


def generate_verification_corpus(output_dir: str = "tests/verification_corpus"):
    """Generate a comprehensive verification corpus"""
    import os

    os.makedirs(output_dir, exist_ok=True)

    configs = [
        # Small user counts
        ScenarioConfig(num_users=8, num_transactions=100, seed=1001),
        ScenarioConfig(num_users=16, num_transactions=200, seed=1002),

        # Medium user counts with different distributions
        ScenarioConfig(num_users=64, num_transactions=1000,
                      opcode_dist=OpcodeDistribution.TRANSFER_HEAVY, seed=2001),
        ScenarioConfig(num_users=64, num_transactions=1000,
                      opcode_dist=OpcodeDistribution.SWAP_HEAVY, seed=2002),
        ScenarioConfig(num_users=64, num_transactions=1000,
                      role_dist=RoleDistribution.CLIENT_HEAVY, seed=2003),

        # Large user counts
        ScenarioConfig(num_users=256, num_transactions=5000, seed=3001),
        ScenarioConfig(num_users=1024, num_transactions=10000, seed=3002),

        # Amount distributions
        ScenarioConfig(num_users=64, num_transactions=1000,
                      amount_dist=AmountDistribution.SMALL, seed=4001),
        ScenarioConfig(num_users=64, num_transactions=1000,
                      amount_dist=AmountDistribution.VERY_LARGE, seed=4002),

        # Time patterns
        ScenarioConfig(num_users=64, num_transactions=1000,
                      time_pattern=TimePattern.BURSTY, seed=5001),
        ScenarioConfig(num_users=64, num_transactions=1000,
                      time_pattern=TimePattern.SESSION_GAPS, seed=5002),

        # Hazard injection (pipeline stress)
        ScenarioConfig(num_users=32, num_transactions=500,
                      hazard_probability=0.3, seed=6001),
        ScenarioConfig(num_users=16, num_transactions=200,
                      hazard_probability=0.5, seed=6002),

        # Edge case injection
        ScenarioConfig(num_users=64, num_transactions=1000,
                      edge_case_probability=0.1, seed=7001),

        # Degenerate cases
        ScenarioConfig(num_users=64, num_transactions=500,
                      opcode_dist=OpcodeDistribution.DEGENERATE, seed=8001),
        ScenarioConfig(num_users=64, num_transactions=500,
                      role_dist=RoleDistribution.DEGENERATE, seed=8002),
    ]

    print(f"Generating {len(configs)} verification scenarios...")

    for i, config in enumerate(configs):
        generator = ScenarioGenerator(config)
        transactions = generator.generate()

        # Save to CSV
        filename = f"{output_dir}/scenario_{i+1:03d}_u{config.num_users}_n{config.num_transactions}.csv"

        with open(filename, 'w') as f:
            # Write header
            f.write("timestamp,user_a,user_b,asset0_amount,asset1_amount,opcode,role_a,role_b\n")

            # Write transactions
            for tx in transactions:
                f.write(f"{tx.timestamp},{tx.user_a},{tx.user_b},{tx.asset0_amount},"
                       f"{tx.asset1_amount},{tx.opcode},{tx.role_a},{tx.role_b}\n")

        print(f"  [{i+1:2d}/{len(configs)}] {filename}")
        print(generator.get_coverage_report())
        print()

    print(f"✅ Generated {len(configs)} scenarios in {output_dir}/")


if __name__ == "__main__":
    generate_verification_corpus()
