"""
Protocol Mappers - Chain-Agnostic Transaction Normalization

This module provides pure functions that convert protocol-specific transaction
formats into the canonical SentinelTx schema.

Supported protocols:
- Solana: Mainnet transfers and swaps
- EVM (ERC-20): Ethereum/Arbitrum/Polygon token transfers
- DePIN Rewards: Generic emission/reward transactions (Helium, Filecoin, Render)

Each mapper is a pure function: same input → same output (deterministic).
No side effects, no global state, no randomness.
"""

import hashlib
from typing import Dict, Callable
from .schema import SentinelTx, Opcode


def hash_address_to_user_id(address: str, num_users: int = 1024) -> int:
    """
    Hash an external address (Solana pubkey, EVM address) to user ID.

    Uses SHA-256 to deterministically map addresses to [0, num_users).

    Args:
        address: External address string (pubkey, hex address, etc.)
        num_users: Address space size (default 1024)

    Returns:
        int: User ID in range [0, num_users)

    Collision Probability:
        With 1024 buckets and N addresses, collision probability ≈ N²/(2*1024)
        For N=10000 addresses: ≈48.8% chance of at least one collision
        For N=1000 addresses: ≈5.6% chance of at least one collision

    Mitigation:
        - Increase num_users (1024 → 4096 → 16384)
        - Track top N addresses explicitly (no hashing)
        - Document collision impact on whale metrics
    """
    # Use SHA-256 for good distribution
    hash_bytes = hashlib.sha256(address.encode('utf-8')).digest()
    # Convert first 8 bytes to int
    hash_int = int.from_bytes(hash_bytes[:8], byteorder='big')
    return hash_int % num_users


def normalize_solana(row: Dict, num_users: int = 1024) -> SentinelTx:
    """
    Convert Solana transaction to canonical format.

    Expected input schema (Solana mainnet CSV):
        - block_time OR timestamp: Unix timestamp or ISO format
        - sender: Base58 pubkey
        - receiver: Base58 pubkey
        - amount_usdc: USDC amount (micro-units, 6 decimals)
        - amount_compute: GPU compute credits (optional, 0 if not swap)
        - signature: Transaction signature (hash)
        - slot OR block_height: Block height (optional)

    Mapping logic:
        - If amount_compute > 0: Atomic Swap (opcode=1)
        - If amount_compute == 0: Transfer (opcode=0)

    Args:
        row: Dictionary with Solana transaction fields
        num_users: Address space size

    Returns:
        SentinelTx: Normalized transaction
    """
    sender_id = hash_address_to_user_id(row['sender'], num_users)
    receiver_id = hash_address_to_user_id(row['receiver'], num_users)

    amount_usdc = int(row.get('amount_usdc', 0))
    amount_compute = int(row.get('amount_compute', 0))

    # Determine opcode: swap if compute credits involved, else transfer
    opcode = Opcode.SWAP if amount_compute > 0 else Opcode.TRANSFER

    # Parse timestamp (handle both 'block_time' and 'timestamp' fields)
    timestamp_raw = row.get('block_time') or row.get('timestamp', 0)
    if isinstance(timestamp_raw, str):
        # Try parsing ISO format timestamp
        try:
            from datetime import datetime
            dt = datetime.fromisoformat(timestamp_raw.replace('Z', '+00:00'))
            timestamp = int(dt.timestamp())
        except:
            # Fallback to 0 if parsing fails
            timestamp = 0
    else:
        timestamp = int(timestamp_raw)

    # Parse block height (handle both 'slot' and 'block_height' fields)
    block_height = int(row.get('slot') or row.get('block_height', 0))

    return SentinelTx(
        timestamp=timestamp,
        user_a=sender_id,
        user_b=receiver_id,
        asset0_amount=amount_usdc,
        asset1_amount=amount_compute,
        opcode=opcode,
        role_a='client',
        role_b='client',
        tx_hash=row.get('signature', ''),
        block_height=block_height
    )


def normalize_evm_erc20(row: Dict, num_users: int = 1024) -> SentinelTx:
    """
    Convert EVM ERC-20 transfer to canonical format.

    Expected input schema (Ethereum/Arbitrum/Polygon):
        - block_timestamp: Unix timestamp
        - from: Hex address (0x...)
        - to: Hex address (0x...)
        - value: Token amount in wei/smallest unit
        - transaction_hash: Transaction hash
        - block_number: Block height

    Mapping logic:
        - All ERC-20 transfers map to opcode=0 (Transfer)
        - asset1_amount always 0 (single-asset transfers)

    Args:
        row: Dictionary with EVM transaction fields
        num_users: Address space size

    Returns:
        SentinelTx: Normalized transaction
    """
    from_id = hash_address_to_user_id(row['from'], num_users)
    to_id = hash_address_to_user_id(row['to'], num_users)

    amount_wei = int(row.get('value', 0))

    return SentinelTx(
        timestamp=int(row['block_timestamp']),
        user_a=from_id,
        user_b=to_id,
        asset0_amount=amount_wei,
        asset1_amount=0,
        opcode=Opcode.TRANSFER,
        role_a='client',
        role_b='client',
        tx_hash=row.get('transaction_hash', ''),
        block_height=int(row.get('block_number', 0))
    )


def normalize_depin_rewards(row: Dict, num_users: int = 1024) -> SentinelTx:
    """
    Convert DePIN protocol rewards/emissions to canonical format.

    Expected input schema (Helium, Filecoin, Render, etc.):
        - epoch: Timestamp or epoch number
        - node_id: Node identifier (hotspot ID, miner ID, etc.)
        - reward_amount: Reward amount in protocol tokens
        - node_type: Optional role (miner, validator, hotspot, etc.)

    Mapping logic:
        - user_a = 0 (protocol treasury)
        - user_b = hashed node_id
        - opcode = 2 (Reward)
        - asset0 = reward amount
        - asset1 = 0 (no dual-asset in rewards)

    Args:
        row: Dictionary with DePIN reward fields
        num_users: Address space size

    Returns:
        SentinelTx: Normalized transaction
    """
    node_id = hash_address_to_user_id(row['node_id'], num_users)
    reward_amount = int(row.get('reward_amount', 0))
    node_type = row.get('node_type', 'miner')

    return SentinelTx(
        timestamp=int(row.get('epoch', 0)),
        user_a=0,  # Protocol treasury (fixed ID 0)
        user_b=node_id,
        asset0_amount=reward_amount,
        asset1_amount=0,
        opcode=Opcode.REWARD,
        role_a='treasury',
        role_b=node_type,
        tx_hash=row.get('tx_hash', ''),
        block_height=int(row.get('block_height', 0))
    )


def normalize_depin_penalty(row: Dict, num_users: int = 1024) -> SentinelTx:
    """
    Convert DePIN protocol penalties/slashing to canonical format.

    Expected input schema:
        - epoch: Timestamp
        - node_id: Node being penalized
        - penalty_amount: Slash amount
        - reason: Optional penalty reason

    Mapping logic:
        - user_a = node_id (being slashed)
        - user_b = 0 (protocol treasury)
        - opcode = 3 (Penalty)

    Args:
        row: Dictionary with penalty fields
        num_users: Address space size

    Returns:
        SentinelTx: Normalized transaction
    """
    node_id = hash_address_to_user_id(row['node_id'], num_users)
    penalty_amount = int(row.get('penalty_amount', 0))

    return SentinelTx(
        timestamp=int(row.get('epoch', 0)),
        user_a=node_id,
        user_b=0,  # Protocol treasury
        asset0_amount=penalty_amount,
        asset1_amount=0,
        opcode=Opcode.PENALTY,
        role_a=row.get('node_type', 'miner'),
        role_b='treasury',
        tx_hash=row.get('tx_hash', ''),
        block_height=int(row.get('block_height', 0))
    )


# Mapper registry - maps protocol names to mapper functions
MAPPERS: Dict[str, Callable[[Dict, int], SentinelTx]] = {
    'solana': normalize_solana,
    'evm': normalize_evm_erc20,
    'evm_erc20': normalize_evm_erc20,
    'ethereum': normalize_evm_erc20,
    'arbitrum': normalize_evm_erc20,
    'polygon': normalize_evm_erc20,
    'depin': normalize_depin_rewards,
    'depin_rewards': normalize_depin_rewards,
    'depin_penalty': normalize_depin_penalty,
    'helium': normalize_depin_rewards,
    'filecoin': normalize_depin_rewards,
    'render': normalize_depin_rewards,
}


def get_mapper(protocol: str) -> Callable[[Dict, int], SentinelTx]:
    """
    Get mapper function for a protocol.

    Args:
        protocol: Protocol name (solana, evm, depin, etc.)

    Returns:
        Callable: Mapper function

    Raises:
        ValueError: If protocol not supported
    """
    protocol_lower = protocol.lower()
    if protocol_lower not in MAPPERS:
        supported = ', '.join(MAPPERS.keys())
        raise ValueError(f"Unsupported protocol: {protocol}. Supported: {supported}")
    return MAPPERS[protocol_lower]
