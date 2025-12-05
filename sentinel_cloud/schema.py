"""
Sentinel Cloud Canonical Transaction Schema

This module defines the universal transaction format that all protocol-specific
transactions are normalized into before simulation.

The canonical schema is chain-agnostic - it works for any dual-asset economy:
- DePIN: GPU compute (Render), storage (Filecoin), IoT (Helium)
- DeFi: DEX swaps, liquidity pools, lending
- Gaming: Gold + gems, XP + items
- L2s: Fee optimization, sequencer revenue
"""

from dataclasses import dataclass
from typing import Optional
from enum import IntEnum


@dataclass
class SentinelTx:
    """
    Universal transaction format for Sentinel Cloud simulations.

    All external transaction data (Solana, EVM, DePIN protocols) is normalized
    into this format before being replayed through the hardware engine.

    Asset Semantics (Critical Convention):
        asset0_amount: ALWAYS the unit of account (money token)
            - Examples: USDC, FIL, HNT, ETH, SOL, MATIC
            - Used for economic metrics (revenue, volume, fees)

        asset1_amount: ALWAYS the resource/utility token (if dual-asset)
            - Examples: GPU credits, storage bytes, bandwidth, compute units
            - Set to 0 for single-asset transfers
            - Non-zero indicates atomic swap (opcode=1)

    Fields:
        timestamp: Unix timestamp in seconds (or milliseconds, normalized by mapper)
        user_a: Sender user ID (0..NUM_USERS-1, hashed from address)
        user_b: Recipient user ID (0..NUM_USERS-1, hashed from address)
        asset0_amount: Money token amount (unit of account) - see Asset Semantics
        asset1_amount: Resource token amount (utility) - see Asset Semantics
        opcode: Transaction type (use Opcode enum):
            - Opcode.TRANSFER (0): A → B, asset0 only
            - Opcode.SWAP (1): A ↔ B, bidirectional asset0 ↔ asset1
            - Opcode.REWARD (2): Protocol treasury → user
            - Opcode.PENALTY (3): User → protocol treasury
        role_a: Optional role of user_a (see VALID_ROLES)
        role_b: Optional role of user_b (see VALID_ROLES)
        tx_hash: Original transaction hash (for audit trail)
        block_height: Original block number (for temporal analysis)

    Note on User ID Mapping:
        External addresses (Solana pubkeys, EVM addresses) are hashed to fit
        NUM_USERS address space (default 1024). This means:
        - Multiple real addresses may map to same user_id (collision possible)
        - Behavioral patterns preserved, but individual identity may be lost
        - For whale analysis, increase NUM_USERS or track top addresses explicitly

    Example (Solana Transfer):
        SentinelTx(
            timestamp=1234567890,
            user_a=42,  # hash("SenderPubkey") % 1024
            user_b=123,  # hash("RecipientPubkey") % 1024
            asset0_amount=1000000,  # 1 USDC (6 decimals)
            asset1_amount=0,
            opcode=0,  # Transfer
            role_a="client",
            role_b="client",
            tx_hash="5KHx...",
            block_height=150000000
        )

    Example (DePIN Reward):
        SentinelTx(
            timestamp=1234567890,
            user_a=0,  # Protocol treasury
            user_b=567,  # Miner node
            asset0_amount=50000,  # 50K reward tokens
            asset1_amount=0,
            opcode=2,  # Reward
            role_a="treasury",
            role_b="miner",
            tx_hash="abc123...",
            block_height=500
        )
    """

    # Core fields (required)
    timestamp: int
    user_a: int
    user_b: int
    asset0_amount: int
    asset1_amount: int
    opcode: int

    # Optional metadata
    role_a: str = ""
    role_b: str = ""
    tx_hash: str = ""
    block_height: int = 0

    def validate(self, num_users: int = 1024, strict_roles: bool = True) -> bool:
        """
        Validate transaction fields.

        Args:
            num_users: Maximum user ID (default 1024)
            strict_roles: Enforce role validation against VALID_ROLES (default True)

        Returns:
            bool: True if valid, False otherwise

        Validation rules:
            - user_a, user_b in [0, num_users)
            - amounts >= 0
            - opcode in [Opcode.TRANSFER, Opcode.SWAP, Opcode.REWARD, Opcode.PENALTY]
            - timestamp >= 0
            - roles in VALID_ROLES (if strict_roles=True)
        """
        if not (0 <= self.user_a < num_users):
            return False
        if not (0 <= self.user_b < num_users):
            return False
        if self.asset0_amount < 0 or self.asset1_amount < 0:
            return False
        if not (Opcode.TRANSFER <= self.opcode <= Opcode.PENALTY):
            return False
        if self.timestamp < 0:
            return False
        if strict_roles:
            if not validate_role(self.role_a):
                return False
            if not validate_role(self.role_b):
                return False
        return True

    def to_csv_row(self) -> dict:
        """
        Convert to CSV-compatible dictionary.

        Returns:
            dict: Row data for CSV export
        """
        return {
            'timestamp': self.timestamp,
            'user_a': self.user_a,
            'user_b': self.user_b,
            'asset0_amount': self.asset0_amount,
            'asset1_amount': self.asset1_amount,
            'opcode': self.opcode,
            'role_a': self.role_a,
            'role_b': self.role_b,
            'tx_hash': self.tx_hash,
            'block_height': self.block_height
        }

    @classmethod
    def from_csv_row(cls, row: dict):
        """
        Create SentinelTx from CSV row.

        Args:
            row: Dictionary with column names as keys

        Returns:
            SentinelTx: Parsed transaction
        """
        return cls(
            timestamp=int(row['timestamp']),
            user_a=int(row['user_a']),
            user_b=int(row['user_b']),
            asset0_amount=int(row['asset0_amount']),
            asset1_amount=int(row['asset1_amount']),
            opcode=int(row['opcode']),
            role_a=row.get('role_a', ''),
            role_b=row.get('role_b', ''),
            tx_hash=row.get('tx_hash', ''),
            block_height=int(row.get('block_height', 0))
        )


# Canonical CSV column order
CANONICAL_CSV_COLUMNS = [
    'timestamp',
    'user_a',
    'user_b',
    'asset0_amount',
    'asset1_amount',
    'opcode',
    'role_a',
    'role_b',
    'tx_hash',
    'block_height'
]


# Opcode enum for type safety
class Opcode(IntEnum):
    """
    Transaction operation codes.

    Using IntEnum ensures type safety while maintaining compatibility with
    hardware testbench (expects integer opcodes).
    """
    TRANSFER = 0  # A → B (asset0 only, single-direction)
    SWAP = 1      # A ↔ B (bidirectional asset0 ↔ asset1, atomic)
    REWARD = 2    # Protocol → User (emission, treasury payout)
    PENALTY = 3   # User → Protocol (slash, fee, burn)


# Valid role identifiers
VALID_ROLES = {
    "",                    # Empty = unspecified (default)
    "client",             # Regular user/customer
    "miner",              # Proof-of-work participant
    "validator",          # Proof-of-stake participant
    "treasury",           # Protocol-controlled account
    "hotspot",            # IoT device (Helium)
    "storage_provider",   # Storage network node (Filecoin)
    "sequencer",          # L2 block producer
    "lp",                 # Liquidity provider
}


def validate_role(role: str) -> bool:
    """
    Validate role string against known roles.

    Args:
        role: Role identifier string

    Returns:
        bool: True if valid, False otherwise

    Note:
        Empty string ("") is valid (means role unspecified).
        Validation is case-sensitive.
    """
    return role in VALID_ROLES
