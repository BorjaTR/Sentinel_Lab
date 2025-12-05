"""
Unit tests for protocol mappers.

Tests verify:
- Determinism (same input → same output)
- Range validation (user IDs within bounds)
- Opcode correctness
- Role preservation
- Collision handling
"""

import pytest
from sentinel_cloud.mappers import (
    normalize_solana,
    normalize_evm_erc20,
    normalize_depin_rewards,
    normalize_depin_penalty,
    hash_address_to_user_id
)
from sentinel_cloud.schema import SentinelTx, Opcode


class TestHashAddressToUserId:
    """Test address hashing function."""

    def test_determinism(self):
        """Same address should always hash to same user_id."""
        address = "SolAddress0001abcdef"
        user_id_1 = hash_address_to_user_id(address, num_users=1024)
        user_id_2 = hash_address_to_user_id(address, num_users=1024)
        assert user_id_1 == user_id_2

    def test_range_validation(self):
        """User ID should be within [0, num_users)."""
        address = "0x742d35Cc6634C0532925a3b844Bc9e7595f0bEb"
        for num_users in [1024, 4096, 16384]:
            user_id = hash_address_to_user_id(address, num_users)
            assert 0 <= user_id < num_users

    def test_different_addresses_can_collide(self):
        """Different addresses MAY map to same user_id (collision possible)."""
        addr1 = "address1"
        addr2 = "address2"
        id1 = hash_address_to_user_id(addr1, num_users=2)  # Small space → high collision
        id2 = hash_address_to_user_id(addr2, num_users=2)
        # Both should be valid, collision is OK
        assert 0 <= id1 < 2
        assert 0 <= id2 < 2

    def test_distribution(self):
        """Hash should distribute addresses across buckets."""
        addresses = [f"address_{i}" for i in range(100)]
        user_ids = [hash_address_to_user_id(addr, 1024) for addr in addresses]
        unique_ids = set(user_ids)
        # Should use at least 50% of address space (probabilistic, not guaranteed)
        assert len(unique_ids) >= 50


class TestNormalizeSolana:
    """Test Solana mapper."""

    def test_transfer_basic(self):
        """Test basic USDC transfer (no swap)."""
        row = {
            'timestamp': '2025-12-02T15:24:10',
            'sender': 'SolAddress0001',
            'receiver': 'SolAddress0002',
            'amount_usdc': 1000000,  # 1 USDC (6 decimals)
            'amount_compute': 0,
            'signature': 'sig123abc'
        }
        tx = normalize_solana(row, num_users=1024)

        assert tx.asset0_amount == 1000000
        assert tx.asset1_amount == 0
        assert tx.opcode == Opcode.TRANSFER
        assert 0 <= tx.user_a < 1024
        assert 0 <= tx.user_b < 1024
        assert tx.role_a == 'client'
        assert tx.role_b == 'client'
        assert tx.tx_hash == 'sig123abc'
        assert tx.validate(num_users=1024)

    def test_swap_detection(self):
        """Test swap detection when amount_compute > 0."""
        row = {
            'timestamp': '2025-12-02T15:24:10',
            'sender': 'SolAddr1',
            'receiver': 'SolAddr2',
            'amount_usdc': 50000,
            'amount_compute': 100,  # Non-zero → SWAP
            'signature': 'sig_swap'
        }
        tx = normalize_solana(row, num_users=1024)

        assert tx.opcode == Opcode.SWAP
        assert tx.asset0_amount == 50000
        assert tx.asset1_amount == 100

    def test_timestamp_iso_format(self):
        """Test ISO 8601 timestamp parsing."""
        row = {
            'timestamp': '2025-12-02T15:24:10.407030',
            'sender': 'A',
            'receiver': 'B',
            'amount_usdc': 100,
            'amount_compute': 0
        }
        tx = normalize_solana(row)
        assert tx.timestamp > 0  # Successfully parsed

    def test_timestamp_unix_format(self):
        """Test Unix timestamp (already integer)."""
        row = {
            'block_time': 1701532800,
            'sender': 'A',
            'receiver': 'B',
            'amount_usdc': 100,
            'amount_compute': 0
        }
        tx = normalize_solana(row)
        assert tx.timestamp == 1701532800

    def test_determinism(self):
        """Same input should produce same output."""
        row = {
            'timestamp': '2025-12-02T15:24:10',
            'sender': 'SolSender',
            'receiver': 'SolReceiver',
            'amount_usdc': 5000,
            'amount_compute': 25
        }
        tx1 = normalize_solana(row, num_users=1024)
        tx2 = normalize_solana(row, num_users=1024)

        assert tx1.user_a == tx2.user_a
        assert tx1.user_b == tx2.user_b
        assert tx1.asset0_amount == tx2.asset0_amount
        assert tx1.asset1_amount == tx2.asset1_amount
        assert tx1.opcode == tx2.opcode


class TestNormalizeEVM:
    """Test EVM ERC-20 mapper."""

    def test_erc20_transfer(self):
        """Test basic ERC-20 transfer."""
        row = {
            'block_timestamp': 1701532800,
            'from': '0x742d35Cc6634C0532925a3b844Bc9e7595f0bEb',
            'to': '0x8Ba1f109551bD432803012645Ac136ddd64DBA72',
            'value': 1000000000000000000,  # 1 token (18 decimals)
            'transaction_hash': '0xabc123',
            'block_number': 18500000
        }
        tx = normalize_evm_erc20(row, num_users=1024)

        assert tx.asset0_amount == 1000000000000000000
        assert tx.asset1_amount == 0  # EVM transfers are single-asset
        assert tx.opcode == Opcode.TRANSFER
        assert 0 <= tx.user_a < 1024
        assert 0 <= tx.user_b < 1024
        assert tx.role_a == 'client'
        assert tx.role_b == 'client'
        assert tx.tx_hash == '0xabc123'
        assert tx.block_height == 18500000
        assert tx.validate(num_users=1024)

    def test_determinism(self):
        """Same EVM transaction should produce same result."""
        row = {
            'block_timestamp': 1701532800,
            'from': '0xFromAddress',
            'to': '0xToAddress',
            'value': 5000000
        }
        tx1 = normalize_evm_erc20(row)
        tx2 = normalize_evm_erc20(row)

        assert tx1.user_a == tx2.user_a
        assert tx1.user_b == tx2.user_b


class TestNormalizeDePINRewards:
    """Test DePIN rewards mapper."""

    def test_reward_basic(self):
        """Test basic protocol reward."""
        row = {
            'epoch': 1701532800,
            'node_id': 'hotspot_abc123',
            'reward_amount': 50000,
            'node_type': 'hotspot'
        }
        tx = normalize_depin_rewards(row, num_users=1024)

        assert tx.user_a == 0  # Treasury
        assert 0 < tx.user_b < 1024  # Hashed node_id (shouldn't be 0)
        assert tx.asset0_amount == 50000
        assert tx.asset1_amount == 0
        assert tx.opcode == Opcode.REWARD
        assert tx.role_a == 'treasury'
        assert tx.role_b == 'hotspot'
        assert tx.validate(num_users=1024)

    def test_treasury_is_zero(self):
        """Treasury should always be user_id=0."""
        row = {
            'epoch': 1701532800,
            'node_id': 'miner_xyz',
            'reward_amount': 100000,
            'node_type': 'miner'
        }
        tx = normalize_depin_rewards(row)
        assert tx.user_a == 0

    def test_role_preservation(self):
        """Node type should be preserved in role_b."""
        for node_type in ['miner', 'validator', 'hotspot', 'storage_provider']:
            row = {
                'epoch': 1701532800,
                'node_id': f'node_{node_type}',
                'reward_amount': 1000,
                'node_type': node_type
            }
            tx = normalize_depin_rewards(row)
            assert tx.role_b == node_type

    def test_determinism(self):
        """Same reward should produce same result."""
        row = {
            'epoch': 1701532800,
            'node_id': 'node123',
            'reward_amount': 75000
        }
        tx1 = normalize_depin_rewards(row)
        tx2 = normalize_depin_rewards(row)

        assert tx1.user_b == tx2.user_b
        assert tx1.asset0_amount == tx2.asset0_amount


class TestNormalizeDePINPenalty:
    """Test DePIN penalty mapper."""

    def test_penalty_basic(self):
        """Test basic slashing penalty."""
        row = {
            'epoch': 1701532800,
            'node_id': 'validator_bad',
            'penalty_amount': 10000,
            'node_type': 'validator'
        }
        tx = normalize_depin_penalty(row, num_users=1024)

        assert 0 < tx.user_a < 1024  # Hashed node_id
        assert tx.user_b == 0  # Treasury receives penalty
        assert tx.asset0_amount == 10000
        assert tx.asset1_amount == 0
        assert tx.opcode == Opcode.PENALTY
        assert tx.role_b == 'treasury'
        assert tx.validate(num_users=1024)

    def test_treasury_receives_penalty(self):
        """Penalties should always go to treasury (user_id=0)."""
        row = {
            'epoch': 1701532800,
            'node_id': 'bad_miner',
            'penalty_amount': 5000
        }
        tx = normalize_depin_penalty(row)
        assert tx.user_b == 0

    def test_determinism(self):
        """Same penalty should produce same result."""
        row = {
            'epoch': 1701532800,
            'node_id': 'penalized_node',
            'penalty_amount': 25000
        }
        tx1 = normalize_depin_penalty(row)
        tx2 = normalize_depin_penalty(row)

        assert tx1.user_a == tx2.user_a
        assert tx1.asset0_amount == tx2.asset0_amount


class TestValidation:
    """Test transaction validation across all mappers."""

    def test_solana_validation(self):
        """Solana transactions should pass validation."""
        row = {
            'timestamp': '2025-12-02T15:24:10',
            'sender': 'A',
            'receiver': 'B',
            'amount_usdc': 1000,
            'amount_compute': 0
        }
        tx = normalize_solana(row, num_users=1024)
        assert tx.validate(num_users=1024, strict_roles=True)

    def test_evm_validation(self):
        """EVM transactions should pass validation."""
        row = {
            'block_timestamp': 1701532800,
            'from': '0xFrom',
            'to': '0xTo',
            'value': 1000
        }
        tx = normalize_evm_erc20(row, num_users=1024)
        assert tx.validate(num_users=1024, strict_roles=True)

    def test_depin_reward_validation(self):
        """DePIN rewards should pass validation."""
        row = {
            'epoch': 1701532800,
            'node_id': 'node1',
            'reward_amount': 1000,
            'node_type': 'miner'
        }
        tx = normalize_depin_rewards(row, num_users=1024)
        assert tx.validate(num_users=1024, strict_roles=True)

    def test_depin_penalty_validation(self):
        """DePIN penalties should pass validation."""
        row = {
            'epoch': 1701532800,
            'node_id': 'node2',
            'penalty_amount': 500,
            'node_type': 'validator'
        }
        tx = normalize_depin_penalty(row, num_users=1024)
        assert tx.validate(num_users=1024, strict_roles=True)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
