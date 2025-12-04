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


@dataclass
class SentinelTx:
    """
    Universal transaction format for Sentinel Cloud simulations.

    All external transaction data (Solana, EVM, DePIN protocols) is normalized
    into this format before being replayed through the hardware engine.

    Fields:
        timestamp: Unix timestamp in seconds (or milliseconds, normalized by mapper)
        user_a: Sender user ID (0..NUM_USERS-1, hashed from address)
        user_b: Recipient user ID (0..NUM_USERS-1, hashed from address)
        asset0_amount: Money token amount (USDC, FIL, HNT, ETH, etc.)
        asset1_amount: Resource credit amount (GPU, storage, bandwidth, etc.)
        opcode: Transaction type:
            - 0: Transfer (A → B, asset0 only)
            - 1: Atomic Swap (A ↔ B, bidirectional asset0 ↔ asset1)
            - 2: Reward/Emission (protocol treasury → user)
            - 3: Penalty/Slash (user → protocol treasury)
        role_a: Optional role of user_a ("client", "miner", "validator", "treasury")
        role_b: Optional role of user_b
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

    def validate(self, num_users: int = 1024) -> bool:
        """
        Validate transaction fields.

        Args:
            num_users: Maximum user ID (default 1024)

        Returns:
            bool: True if valid, False otherwise

        Validation rules:
            - user_a, user_b in [0, num_users)
            - amounts >= 0
            - opcode in [0, 3]
            - timestamp >= 0
        """
        if not (0 <= self.user_a < num_users):
            return False
        if not (0 <= self.user_b < num_users):
            return False
        if self.asset0_amount < 0 or self.asset1_amount < 0:
            return False
        if not (0 <= self.opcode <= 3):
            return False
        if self.timestamp < 0:
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


# Opcode constants for readability
class Opcode:
    """Transaction operation codes"""
    TRANSFER = 0  # A → B (asset0 only)
    SWAP = 1      # A ↔ B (bidirectional asset0 ↔ asset1)
    REWARD = 2    # Protocol → User (emission)
    PENALTY = 3   # User → Protocol (slash)
