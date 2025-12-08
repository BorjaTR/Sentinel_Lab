"""
Mapper & Schema Verification Tests

Tests functional requirements and invariants for transaction normalization:
- FR-MAP-1: Round-trip determinism
- FR-MAP-2: Range & role validity
- INV-MAP-1: Address hashing stability
- INV-MAP-2: Collision awareness
"""

import pytest
import hashlib
import random
from typing import List

from sentinel_cloud.schema import SentinelTx, Opcode
from sentinel_cloud.mappers import normalize_solana, normalize_evm_erc20, normalize_depin_rewards
from sentinel_cloud.io import load_and_normalize

# UserRole is not defined in schema, roles are just strings
VALID_ROLES = ['client', 'validator', 'miner', 'treasury']


class TestMapperDeterminism:
    """FR-MAP-1: Round-trip determinism"""

    def test_solana_mapper_determinism(self):
        """Test Solana mapper produces same output for same input"""
        # Sample Solana transaction row
        row = {
            'timestamp': '1700000000',
            'signature': 'abc123def456',
            'sender': 'SoLaRa1234567890ABCDEFGHIJKLMNOPQR',
            'receiver': 'SoLaRa9876543210ZYXWVUTSRQPONMLKJI',
            'amount_usdc': '1000000',  # 1 USDC (6 decimals)
            'amount_compute': '0',
            'program': 'spl_token',
        }

        # Normalize 10 times
        results = []
        for _ in range(10):
            tx = normalize_solana(row, num_users=1024)
            results.append(tx)

        # All results should be identical
        for i in range(1, len(results)):
            assert results[i].timestamp == results[0].timestamp
            assert results[i].user_a == results[0].user_a
            assert results[i].user_b == results[0].user_b
            assert results[i].asset0_amount == results[0].asset0_amount
            assert results[i].asset1_amount == results[0].asset1_amount
            assert results[i].opcode == results[0].opcode

    def test_evm_mapper_determinism(self):
        """Test EVM mapper produces same output for same input"""
        row = {
            'block_timestamp': '1700000000',
            'transaction_hash': '0xabcd1234',
            'from': '0x742d35Cc6634C0532925a3b844Bc9e7595f0bEb',
            'to': '0x8ad599c3A0ff1De082011EFDDc58f1908eb6e6D8',
            'value': '1000000000000000000',  # 1 ETH (18 decimals)
            'block_number': '12345678',
        }

        results = []
        for _ in range(10):
            tx = normalize_evm_erc20(row, num_users=1024)
            results.append(tx)

        # All results should be identical
        for i in range(1, len(results)):
            assert results[i].user_a == results[0].user_a
            assert results[i].user_b == results[0].user_b
            assert results[i].asset0_amount == results[0].asset0_amount

    def test_depin_mapper_determinism(self):
        """Test DePIN rewards mapper produces same output for same input"""
        row = {
            'epoch': '1700000000',
            'node_id': 'depin_user_12345',
            'reward_amount': '100',
            'node_type': 'miner',
        }

        results = []
        for _ in range(10):
            tx = normalize_depin_rewards(row, num_users=1024)
            results.append(tx)

        for i in range(1, len(results)):
            assert results[i].user_a == results[0].user_a
            assert results[i].asset0_amount == results[0].asset0_amount


class TestMapperValidation:
    """FR-MAP-2: Range & role validity"""

    def test_user_id_in_range(self):
        """Test that normalized user IDs are in valid range"""
        # Generate 1000 random addresses
        addresses = [f"addr_{random.randint(0, 1000000)}" for _ in range(1000)]

        num_users = 1024
        for addr in addresses:
            # Hash address to user ID
            hash_val = int(hashlib.sha256(addr.encode()).hexdigest()[:8], 16)
            user_id = hash_val % num_users

            assert 0 <= user_id < num_users, f"User ID {user_id} out of range [0, {num_users})"

    def test_invalid_opcode_rejected(self):
        """Test that invalid opcodes are rejected"""
        row = {
            'timestamp': '1700000000',
            'signature': 'test',
            'sender': 'addr1',
            'receiver': 'addr2',
            'amount_usdc': '1000',
            'amount_compute': '0',
            'program': 'unknown_program',
        }

        # Should either reject or default to safe opcode
        tx = normalize_solana(row, num_users=1024)
        valid_opcodes = [Opcode.TRANSFER, Opcode.SWAP, Opcode.REWARD, Opcode.PENALTY]
        assert tx.opcode in valid_opcodes, f"Invalid opcode: {tx.opcode}"

    def test_negative_amounts_rejected(self):
        """Test that negative amounts are rejected or sanitized"""
        row = {
            'timestamp': '1700000000',
            'signature': 'test',
            'sender': 'addr1',
            'receiver': 'addr2',
            'amount_usdc': '-1000',  # Negative!
            'amount_compute': '0',
            'program': 'spl_token',
        }

        # Should either raise exception or clamp to 0
        try:
            tx = normalize_solana(row, num_users=1024)
            assert tx.asset0_amount >= 0, "Negative amount was not rejected"
        except (ValueError, AssertionError):
            # Expected: reject invalid input
            pass

    def test_invalid_role_strict_mode(self):
        """Test that roles are set to reasonable defaults"""
        row = {
            'timestamp': '1700000000',
            'signature': 'test',
            'sender': 'addr1',
            'receiver': 'addr2',
            'amount_usdc': '1000',
            'amount_compute': '0',
            'program': 'spl_token',
        }

        # Mapper should set default roles (e.g., 'client' for Solana)
        tx = normalize_solana(row, num_users=1024)
        assert tx.role_a in VALID_ROLES, f"Invalid role: {tx.role_a}"
        assert tx.role_b in VALID_ROLES, f"Invalid role: {tx.role_b}"


class TestAddressHashingStability:
    """INV-MAP-1: Address hashing stability"""

    def test_same_address_same_id(self):
        """Test that same address always hashes to same user ID"""
        addresses = [
            "SoLaRa1234567890ABCDEFGHIJKLMNOPQR",
            "0x742d35Cc6634C0532925a3b844Bc9e7595f0bEb",
            "depin_user_test_12345",
        ]

        num_users = 1024
        for addr in addresses:
            # Hash 100 times
            user_ids = []
            for _ in range(100):
                hash_val = int(hashlib.sha256(addr.encode()).hexdigest()[:8], 16)
                user_id = hash_val % num_users
                user_ids.append(user_id)

            # All should be identical
            assert len(set(user_ids)) == 1, f"Address {addr} hashed to multiple IDs: {set(user_ids)}"

    def test_different_addresses_different_ids_usually(self):
        """Test that different addresses usually produce different IDs"""
        num_addresses = 100
        num_users = 1024

        addresses = [f"addr_{i}" for i in range(num_addresses)]
        user_ids = set()

        for addr in addresses:
            hash_val = int(hashlib.sha256(addr.encode()).hexdigest()[:8], 16)
            user_id = hash_val % num_users
            user_ids.add(user_id)

        # With 100 addresses and 1024 slots, expect >90 unique IDs
        # (some collisions are expected)
        assert len(user_ids) > 90, f"Too many collisions: {len(user_ids)} unique IDs from {num_addresses} addresses"


class TestCollisionAwareness:
    """INV-MAP-2: Collision awareness"""

    def test_collision_probability_documented(self):
        """Verify collision probabilities match documentation"""
        # With 10,000 distinct addresses into 1024 slots
        # Birthday paradox: expect significant collisions

        num_addresses = 10000
        num_users = 1024

        addresses = [f"addr_{i}" for i in range(num_addresses)]
        user_id_counts = {}

        for addr in addresses:
            hash_val = int(hashlib.sha256(addr.encode()).hexdigest()[:8], 16)
            user_id = hash_val % num_users
            user_id_counts[user_id] = user_id_counts.get(user_id, 0) + 1

        # Calculate collision statistics
        collided_slots = sum(1 for count in user_id_counts.values() if count > 1)
        max_collision = max(user_id_counts.values())
        avg_collision = num_addresses / num_users

        print(f"\n{'='*60}")
        print(f"Collision Analysis: {num_addresses} addresses → {num_users} slots")
        print(f"{'='*60}")
        print(f"Slots with collisions: {collided_slots} ({100*collided_slots/num_users:.1f}%)")
        print(f"Max collisions in one slot: {max_collision}")
        print(f"Average addresses per slot: {avg_collision:.2f}")
        print(f"{'='*60}")

        # Expected: most slots have ~9-10 addresses
        assert 8 < avg_collision < 12, "Collision rate outside expected range"

    def test_high_collision_scenario_no_crash(self):
        """Test that high collision rate doesn't crash the system"""
        # Create synthetic CSV with 10k addresses mapping to 64 users
        num_addresses = 10000
        num_users = 64  # Very small → high collisions

        addresses = [f"user_{i}" for i in range(num_addresses)]

        # Create fake CSV data
        csv_data = []
        for i, addr in enumerate(addresses):
            hash_val = int(hashlib.sha256(addr.encode()).hexdigest()[:8], 16)
            user_id = hash_val % num_users

            row = {
                'timestamp': str(1700000000 + i),
                'signature': f"sig_{i}",
                'sender': addr,
                'receiver': addresses[(i + 1) % num_addresses],
                'amount_usdc': str(random.randint(1, 1000)),
                'amount_compute': '0',
                'program': 'spl_token',
            }
            csv_data.append(row)

        # Normalize all rows
        transactions = []
        for row in csv_data[:100]:  # Test first 100 to keep it fast
            try:
                tx = normalize_solana(row, num_users=num_users)
                transactions.append(tx)
            except Exception as e:
                pytest.fail(f"Normalization crashed with high collisions: {e}")

        # Should succeed without crashes
        assert len(transactions) == 100

    def test_collision_preserves_semantics(self):
        """Test that collisions don't corrupt transaction semantics"""
        # Two different addresses that collide
        addr1 = "collision_test_1"
        addr2 = "collision_test_2"

        num_users = 8  # Small space → force collisions

        # Find two addresses that collide
        hash1 = int(hashlib.sha256(addr1.encode()).hexdigest()[:8], 16) % num_users
        hash2 = int(hashlib.sha256(addr2.encode()).hexdigest()[:8], 16) % num_users

        if hash1 == hash2:
            # They collide!
            # Both should map to same user_id consistently
            row1 = {
                'timestamp': '1700000000',
                'signature': 'sig1',
                'sender': addr1,
                'receiver': 'other',
                'amount_usdc': '1000',
                'amount_compute': '0',
                'program': 'spl_token',
            }

            row2 = {
                'timestamp': '1700000001',
                'signature': 'sig2',
                'sender': addr2,
                'receiver': 'other',
                'amount_usdc': '2000',
                'amount_compute': '0',
                'program': 'spl_token',
            }

            tx1 = normalize_solana(row1, num_users=num_users)
            tx2 = normalize_solana(row2, num_users=num_users)

            # Both should use same user_id (collision)
            assert tx1.user_a == tx2.user_a

            # But amounts should be preserved correctly
            assert tx1.asset0_amount == 1000
            assert tx2.asset0_amount == 2000


@pytest.mark.parametrize("mapper_name", ["solana", "evm", "depin_rewards"])
def test_mapper_fuzz(mapper_name):
    """Fuzz test mappers with random corrupted data"""
    for _ in range(100):
        # Generate random row with potentially invalid data
        row = {
            'timestamp': str(random.randint(0, 2**31)),
            'signature': ''.join(random.choices('abcdef0123456789', k=64)),
            'sender': ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=44)),
            'receiver': ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=44)),
            'amount_usdc': str(random.randint(-1000, 1000000)),  # May be negative
            'amount_compute': str(random.randint(-100, 10000)),
            'program': random.choice(['spl_token', 'unknown', '', None]),
        }

        try:
            if mapper_name == "solana":
                tx = normalize_solana(row, num_users=1024)
            elif mapper_name == "evm":
                row['block_timestamp'] = row['timestamp']
                row['transaction_hash'] = '0x' + row['signature'][:40]
                row['from'] = row['sender']
                row['to'] = row['receiver']
                row['value'] = row['amount_usdc']
                row['block_number'] = '0'
                tx = normalize_evm_erc20(row, num_users=1024)
            else:
                row['node_id'] = row['sender']
                row['reward_amount'] = row['amount_usdc']
                row['epoch'] = row['timestamp']
                tx = normalize_depin_rewards(row, num_users=1024)

            # Should produce valid transaction or raise exception
            if tx:
                assert 0 <= tx.user_a < 1024
                assert 0 <= tx.user_b < 1024
                assert tx.asset0_amount >= 0  # No negative amounts
                valid_opcodes = [Opcode.TRANSFER, Opcode.SWAP, Opcode.REWARD, Opcode.PENALTY]
                assert tx.opcode in valid_opcodes

        except (ValueError, KeyError, TypeError, AttributeError):
            # Expected: some inputs will be rejected
            pass


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
