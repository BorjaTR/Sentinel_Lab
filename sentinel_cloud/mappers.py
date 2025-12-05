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
    Hash an external address (Solana pubkey, EVM address) to user ID (agent bucket).

    ⚠️  CRITICAL: This creates "agent buckets", NOT 1:1 address mappings.
    Multiple real blockchain addresses will map to the same user_id.

    Uses SHA-256 to deterministically map addresses to [0, num_users).

    Args:
        address: External address string (pubkey, hex address, etc.)
        num_users: Address space size (default 1024)

    Returns:
        int: User ID in range [0, num_users) - represents an "agent bucket"

    Collision Probability (Birthday Paradox):
        Formula: P(collision) ≈ 1 - e^(-N²/(2*num_users))

        | Unique Addresses | num_users=1024 | num_users=4096 | num_users=16384 |
        |------------------|----------------|----------------|-----------------|
        | 1,000            | ~39.3%         | ~11.8%         | ~3.0%           |
        | 5,000            | ~99.2%         | ~86.5%         | ~43.3%          |
        | 10,000           | ~100%          | ~99.3%         | ~86.5%          |
        | 50,000           | ~100%          | ~100%          | ~100%           |

    Implications:
        - "Top 10 users" = "Top 10 agent buckets" (may contain multiple real users)
        - Whale analysis is approximate (whales may share buckets with small users)
        - Behavioral patterns preserved, but individual identity may be lost
        - Transaction ordering within buckets is preserved

    Mitigation Strategies:
        1. Increase num_users (1024 → 4096 → 16384 → 65536)
           - Higher fidelity, but requires more FPGA block RAM
        2. Track top-N addresses explicitly (no hashing for known whales)
        3. Document collision impact in analysis reports
        4. Use sequential mapping for offline analysis (no collisions)

    Design Note:
        This trade-off is intentional - enables hardware acceleration with
        fixed address space while preserving aggregate behavioral patterns.
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

    Mapping Logic:
        - If amount_compute > 0: Atomic Swap (opcode=Opcode.SWAP)
        - If amount_compute == 0: Transfer (opcode=Opcode.TRANSFER)
        - Addresses → user_id via SHA-256 hash (collision-prone)

    Mapping Assumptions:
        ✓ Single-token transfers (direct A → B)
        ✓ Simple atomic swaps (USDC ↔ compute credits)
        ✓ Both Unix timestamps and ISO 8601 format
        ✗ Multi-hop DeFi swaps (Orca, Raydium, Jupiter) - NOT SUPPORTED
        ✗ Inner instructions / program logs - IGNORED
        ✗ NFT transfers - NOT SUPPORTED
        ✗ Complex DeFi primitives (lending, LPs) - NOT SUPPORTED

    Collision Impact:
        - With 1024 buckets and 10K addresses: ~48.8% collision probability
        - Multiple real users may map to same user_id
        - Use num_users=16384 for <3% collision rate with 10K addresses

    Args:
        row: Dictionary with Solana transaction fields
        num_users: Address space size (default 1024)

    Returns:
        SentinelTx: Normalized transaction with roles set to "client"
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

    Supports: Ethereum, Arbitrum, Polygon, Optimism, Base, and all EVM chains.

    Expected input schema (Ethereum/Arbitrum/Polygon):
        - block_timestamp: Unix timestamp
        - from: Hex address (0x...)
        - to: Hex address (0x...)
        - value: Token amount in wei/smallest unit
        - transaction_hash: Transaction hash
        - block_number: Block height

    Mapping Logic:
        - All ERC-20 transfers → opcode=Opcode.TRANSFER
        - asset1_amount always 0 (single-asset only)
        - Addresses → user_id via SHA-256 hash (collision-prone)

    Mapping Assumptions:
        ✓ Simple ERC-20 transfer() calls
        ✓ Single-token transfers (no swaps)
        ✓ Standard Transfer events
        ✗ Uniswap/SushiSwap swaps - NOT SUPPORTED (use custom mapper)
        ✗ Multi-token batches - NOT SUPPORTED
        ✗ NFT transfers (ERC-721, ERC-1155) - NOT SUPPORTED
        ✗ Smart contract interactions beyond transfer() - NOT SUPPORTED

    Collision Impact:
        - Same as Solana mapper (hash-based addressing)
        - Use num_users=16384 for lower collision rate

    Args:
        row: Dictionary with EVM transaction fields
        num_users: Address space size (default 1024)

    Returns:
        SentinelTx: Normalized transaction with roles set to "client"
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

    Supports: Helium, Filecoin, Render, Akash, IoTeX, and similar reward-based protocols.

    Expected input schema (Helium, Filecoin, Render, etc.):
        - epoch: Timestamp or epoch number
        - node_id: Node identifier (hotspot ID, miner ID, etc.)
        - reward_amount: Reward amount in protocol tokens
        - node_type: Optional role (miner, validator, hotspot, etc.)

    Mapping Logic:
        - user_a = 0 (protocol treasury, special address)
        - user_b = hashed node_id
        - opcode = Opcode.REWARD
        - asset0 = reward amount (in protocol tokens)
        - asset1 = 0 (no dual-asset in rewards)

    Mapping Assumptions:
        ✓ Simple protocol → node rewards
        ✓ Fixed treasury address (user_id=0)
        ✓ Node roles preserved (miner, hotspot, validator)
        ✗ Multi-token rewards - NOT SUPPORTED (use asset0 only)
        ✗ Delegation/staking rewards with complex splits - SIMPLIFIED
        ✗ Penalty deductions within rewards - NOT SUPPORTED (use normalize_depin_penalty)

    Treasury Convention:
        - user_id=0 is RESERVED for protocol treasury
        - No real addresses should hash to 0 (probability: 1/num_users)
        - Treasury transactions: Reward (treasury → node) or Penalty (node → treasury)

    Args:
        row: Dictionary with DePIN reward fields
        num_users: Address space size (default 1024)

    Returns:
        SentinelTx: Normalized transaction with role_a="treasury", role_b from node_type
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

    Supports: Proof-of-stake slashing, availability penalties, misconduct fines.

    Expected input schema:
        - epoch: Timestamp
        - node_id: Node being penalized
        - penalty_amount: Slash amount
        - node_type: Optional role (validator, miner, etc.)
        - reason: Optional penalty reason (ignored in normalization)

    Mapping Logic:
        - user_a = hashed node_id (being slashed)
        - user_b = 0 (protocol treasury receives penalty)
        - opcode = Opcode.PENALTY
        - asset0 = penalty amount (slashed tokens)
        - asset1 = 0 (no dual-asset in penalties)

    Mapping Assumptions:
        ✓ Simple node → treasury penalties
        ✓ Fixed treasury address (user_id=0)
        ✓ Single-token slashing
        ✗ Complex multi-party penalties - SIMPLIFIED to node → treasury
        ✗ Partial slashing with redistribution - NOT SUPPORTED
        ✗ Jailing/suspension (non-token penalties) - NOT CAPTURED

    Args:
        row: Dictionary with penalty fields
        num_users: Address space size (default 1024)

    Returns:
        SentinelTx: Normalized transaction with role_b="treasury"
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
