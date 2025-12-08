"""Tests for baseline analysis engine."""

import pytest
from sentinel_cloud.schema import SentinelTx, Opcode
from sentinel_cloud.baseline import BaselineAnalyzer, BaselineMetrics


def test_baseline_empty_transactions():
    """Test baseline with no transactions."""
    analyzer = BaselineAnalyzer()
    result = analyzer.compute([])

    assert result.tx_count == 0
    assert result.total_volume_asset0 == 0.0
    assert result.total_volume_asset1 == 0.0


def test_baseline_basic_aggregation():
    """Test basic volume and count aggregation."""
    txs = [
        SentinelTx(
            timestamp=100,
            user_a=0, user_b=1,
            asset0_amount=1000,
            asset1_amount=0,
            opcode=Opcode.TRANSFER,
            role_a="client", role_b="client"
        ),
        SentinelTx(
            timestamp=200,
            user_a=1, user_b=2,
            asset0_amount=2000,
            asset1_amount=500,
            opcode=Opcode.SWAP,
            role_a="client", role_b="client"
        ),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    assert result.tx_count == 2
    assert result.total_volume_asset0 == 3000
    assert result.total_volume_asset1 == 500
    assert result.transfer_count == 1
    assert result.swap_count == 1
    assert result.reward_count == 0
    assert result.penalty_count == 0


def test_baseline_time_range():
    """Test timestamp range calculation."""
    txs = [
        SentinelTx(
            timestamp=1000, user_a=0, user_b=1, asset0_amount=100,
            asset1_amount=0, opcode=Opcode.TRANSFER, role_a="client", role_b="client"
        ),
        SentinelTx(
            timestamp=5000, user_a=1, user_b=2, asset0_amount=200,
            asset1_amount=0, opcode=Opcode.TRANSFER, role_a="client", role_b="client"
        ),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    assert result.start_timestamp == 1000
    assert result.end_timestamp == 5000
    assert result.duration_seconds == 4000


def test_baseline_daily_rates():
    """Test daily rate calculations."""
    # Create txs spanning exactly 2 days
    day_in_seconds = 86400
    txs = [
        SentinelTx(
            timestamp=0, user_a=0, user_b=1, asset0_amount=1000,
            asset1_amount=0, opcode=Opcode.TRANSFER, role_a="client", role_b="client"
        ),
        SentinelTx(
            timestamp=day_in_seconds * 2, user_a=1, user_b=2, asset0_amount=1000,
            asset1_amount=0, opcode=Opcode.TRANSFER, role_a="client", role_b="client"
        ),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    assert result.daily_volume_asset0 == pytest.approx(1000.0, rel=0.01)
    assert result.daily_tx_count == pytest.approx(1.0, rel=0.01)


def test_baseline_treasury_flow_calculation():
    """Test treasury flow from rewards and penalties."""
    txs = [
        # Protocol pays out rewards (treasury outflow)
        SentinelTx(
            timestamp=100,
            user_a=0,  # Treasury (user_id=0)
            user_b=1,
            asset0_amount=1000,
            asset1_amount=0,
            opcode=Opcode.REWARD,
            role_a="treasury",
            role_b="miner"
        ),
        # User pays penalties (treasury inflow)
        SentinelTx(
            timestamp=200,
            user_a=2,
            user_b=0,  # Treasury
            asset0_amount=500,
            asset1_amount=0,
            opcode=Opcode.PENALTY,
            role_a="validator",
            role_b="treasury"
        ),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    # Net treasury change = penalties - rewards = 500 - 1000 = -500
    # Treasury is bleeding $500 total
    assert result.reward_count == 1
    assert result.penalty_count == 1
    assert result.total_fees_asset0 == 500  # Fees inferred from penalties


def test_baseline_fee_rate_estimation():
    """Test fee rate estimation from penalties and volume."""
    txs = [
        # 10,000 volume in transfers
        SentinelTx(
            timestamp=100,
            user_a=1, user_b=2,
            asset0_amount=10000,
            asset1_amount=0,
            opcode=Opcode.TRANSFER,
            role_a="client", role_b="client"
        ),
        # 100 in penalties (1% of volume)
        SentinelTx(
            timestamp=200,
            user_a=2, user_b=0,
            asset0_amount=100,
            asset1_amount=0,
            opcode=Opcode.PENALTY,
            role_a="client", role_b="treasury"
        ),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    # Total volume = 10000
    # Total fees = 100
    # Fee rate = 100/10000 = 1% = 100 bps
    assert result.total_fees_asset0 == 100
    assert result.avg_fee_rate_asset0 == pytest.approx(100.0, rel=0.01)


def test_baseline_mixed_opcodes():
    """Test transaction breakdown by opcode."""
    txs = [
        SentinelTx(timestamp=100, user_a=1, user_b=2, asset0_amount=100, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
        SentinelTx(timestamp=200, user_a=2, user_b=3, asset0_amount=200, asset1_amount=50,
                   opcode=Opcode.SWAP, role_a="client", role_b="client"),
        SentinelTx(timestamp=300, user_a=0, user_b=4, asset0_amount=300, asset1_amount=0,
                   opcode=Opcode.REWARD, role_a="treasury", role_b="miner"),
        SentinelTx(timestamp=400, user_a=5, user_b=0, asset0_amount=50, asset1_amount=0,
                   opcode=Opcode.PENALTY, role_a="validator", role_b="treasury"),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    assert result.tx_count == 4
    assert result.transfer_count == 1
    assert result.swap_count == 1
    assert result.reward_count == 1
    assert result.penalty_count == 1


def test_baseline_unsorted_transactions():
    """Test that unsorted transactions are handled correctly."""
    txs = [
        SentinelTx(timestamp=500, user_a=1, user_b=2, asset0_amount=100, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
        SentinelTx(timestamp=100, user_a=2, user_b=3, asset0_amount=200, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
        SentinelTx(timestamp=300, user_a=3, user_b=4, asset0_amount=300, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    # Should sort by timestamp internally
    assert result.start_timestamp == 100
    assert result.end_timestamp == 500
    assert result.duration_seconds == 400


def test_baseline_zero_duration():
    """Test handling of transactions with same timestamp."""
    txs = [
        SentinelTx(timestamp=1000, user_a=1, user_b=2, asset0_amount=100, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
        SentinelTx(timestamp=1000, user_a=2, user_b=3, asset0_amount=200, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
    ]

    analyzer = BaselineAnalyzer()
    result = analyzer.compute(txs)

    assert result.start_timestamp == 1000
    assert result.end_timestamp == 1000
    assert result.duration_seconds is None  # No duration if same timestamp
    assert result.daily_volume_asset0 is None  # Can't compute daily rate


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
