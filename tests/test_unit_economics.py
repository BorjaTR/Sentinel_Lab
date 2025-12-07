"""Tests for Unit Economics module."""

import pytest
from sentinel_cloud.unit_economics import (
    UnitEconomicsConfig,
    UnitEconomicsResult,
    compute_unit_economics
)
from sentinel_cloud.schema import SentinelTx, Opcode
from sentinel_cloud.experiment import Config, RunResult
from sentinel_cloud.baseline import BaselineMetrics


def test_unit_economics_config_creation():
    """Test creating a unit economics config."""
    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount",
        include_emissions=True
    )

    assert config.resource_name == "gpu_hour"
    assert config.resource_amount_field == "asset1_amount"
    assert config.include_emissions is True
    assert config.price_per_unit_override is None


def test_compute_unit_economics_basic():
    """Test basic unit economics calculation."""
    # Create test transactions
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,  # $100 payment
            asset1_amount=10,   # 10 GPU hours
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
        SentinelTx(
            timestamp=1001,
            user_a=3,
            user_b=4,
            asset0_amount=200,
            asset1_amount=20,   # 20 GPU hours
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={
            'rev_usdc': 300.0  # $300 total revenue
        }
    )

    baseline = BaselineMetrics(
        tx_count=2,
        total_volume_asset0=300.0,
        total_volume_asset1=30.0,
        duration_seconds=86400  # 1 day
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount"
    )

    result = compute_unit_economics(txs, run, baseline, config)

    # 30 GPU hours total
    assert result.total_units == 30.0
    # $300 revenue
    assert result.total_revenue == 300.0
    # $10 per GPU hour
    assert result.revenue_per_unit == 10.0


def test_compute_unit_economics_with_emissions():
    """Test unit economics with emissions cost."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,
            asset1_amount=10,
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 100.0}
    )

    baseline = BaselineMetrics(
        tx_count=1,
        total_volume_asset0=100.0,
        total_volume_asset1=10.0,
        duration_seconds=86400  # 1 day
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount",
        include_emissions=True
    )

    # $50/day emissions = $5/GPU-hour for 10 GPU hours
    result = compute_unit_economics(
        txs, run, baseline, config,
        emissions_usd_per_day=50.0
    )

    assert result.total_units == 10.0
    assert result.total_revenue == 100.0
    assert result.revenue_per_unit == 10.0

    # $50 total emissions over 1 day
    assert result.total_emissions == 50.0
    assert result.emissions_per_unit == 5.0

    # $100 - $50 = $50 net margin
    assert result.net_margin_total == 50.0
    # $50 / 10 units = $5/unit
    assert result.net_margin_per_unit == 5.0


def test_compute_unit_economics_loss():
    """Test unit economics when making a loss."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,
            asset1_amount=10,
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=10),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 10.0}  # Only $10 revenue
    )

    baseline = BaselineMetrics(
        tx_count=1,
        total_volume_asset0=100.0,
        total_volume_asset1=10.0,
        duration_seconds=86400
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount"
    )

    # $200/day emissions >> $10 revenue
    result = compute_unit_economics(
        txs, run, baseline, config,
        emissions_usd_per_day=200.0
    )

    assert result.revenue_per_unit == 1.0  # $10 / 10 units
    assert result.emissions_per_unit == 20.0  # $200 / 10 units
    assert result.net_margin_per_unit == -19.0  # LOSS of $19/unit


def test_compute_unit_economics_per_role():
    """Test per-role breakdown."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,
            asset1_amount=10,
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
        SentinelTx(
            timestamp=1001,
            user_a=3,
            user_b=4,
            asset0_amount=50,
            asset1_amount=5,
            opcode=Opcode.SWAP,
            role_a="validator",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 150.0}
    )

    baseline = BaselineMetrics(
        tx_count=2,
        total_volume_asset0=150.0,
        total_volume_asset1=15.0,
        duration_seconds=86400
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount"
    )

    result = compute_unit_economics(
        txs, run, baseline, config,
        emissions_usd_per_day=60.0
    )

    # Check per-role breakdown exists
    assert "client" in result.per_role
    assert "validator" in result.per_role

    # Client did 10/15 = 2/3 of units
    client_metrics = result.per_role["client"]
    assert client_metrics["units"] == 10.0
    assert client_metrics["revenue"] == pytest.approx(100.0, rel=0.01)  # 2/3 of $150
    assert client_metrics["emissions"] == pytest.approx(40.0, rel=0.01)  # 2/3 of $60
    assert client_metrics["margin"] == pytest.approx(60.0, rel=0.01)

    # Validator did 5/15 = 1/3 of units
    validator_metrics = result.per_role["validator"]
    assert validator_metrics["units"] == 5.0
    assert validator_metrics["revenue"] == pytest.approx(50.0, rel=0.01)  # 1/3 of $150
    assert validator_metrics["emissions"] == pytest.approx(20.0, rel=0.01)  # 1/3 of $60
    assert validator_metrics["margin"] == pytest.approx(30.0, rel=0.01)


def test_compute_unit_economics_asset0():
    """Test unit economics using asset0 (transactions) as resource."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,  # Resource unit
            asset1_amount=0,
            opcode=Opcode.TRANSFER,
            role_a="client",
            role_b="client"
        ),
        SentinelTx(
            timestamp=1001,
            user_a=3,
            user_b=4,
            asset0_amount=200,
            asset1_amount=0,
            opcode=Opcode.TRANSFER,
            role_a="client",
            role_b="client"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 30.0}
    )

    baseline = BaselineMetrics(
        tx_count=2,
        total_volume_asset0=300.0,
        total_volume_asset1=0.0,
        duration_seconds=86400
    )

    config = UnitEconomicsConfig(
        resource_name="transaction",
        resource_amount_field="asset0_amount"  # Use asset0
    )

    result = compute_unit_economics(txs, run, baseline, config)

    # 300 units (volume)
    assert result.total_units == 300.0
    # $30 revenue
    assert result.total_revenue == 30.0
    # $0.10 per unit
    assert result.revenue_per_unit == pytest.approx(0.10)


def test_compute_unit_economics_zero_units():
    """Test unit economics with zero units."""
    txs = []

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 0.0}
    )

    baseline = BaselineMetrics(
        tx_count=0,
        total_volume_asset0=0.0,
        total_volume_asset1=0.0
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount"
    )

    result = compute_unit_economics(txs, run, baseline, config)

    assert result.total_units == 0
    assert result.revenue_per_unit == 0
    # No emissions provided, so net_margin should be None
    assert result.net_margin_per_unit is None


def test_compute_unit_economics_fees_only():
    """Test unit economics with fees_only flag."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,
            asset1_amount=10,
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 50.0}
    )

    baseline = BaselineMetrics(
        tx_count=1,
        total_volume_asset0=100.0,
        total_volume_asset1=10.0,
        total_fees_asset0=50.0,
        duration_seconds=86400
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount",
        include_fees_only=True
    )

    result = compute_unit_economics(txs, run, baseline, config)

    # Should only use fee revenue
    assert result.total_revenue == 50.0
    assert result.revenue_per_unit == 5.0


def test_compute_unit_economics_summary():
    """Test summary generation."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,
            asset1_amount=10,
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 100.0}
    )

    baseline = BaselineMetrics(
        tx_count=1,
        total_volume_asset0=100.0,
        total_volume_asset1=10.0,
        duration_seconds=86400
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount"
    )

    result = compute_unit_economics(
        txs, run, baseline, config,
        emissions_usd_per_day=50.0
    )

    summary = result.summary()

    assert "UNIT ECONOMICS: gpu_hour" in summary
    assert "Total Units: 10.00" in summary
    assert "Revenue per gpu_hour: $10.0000" in summary
    assert "Emissions per gpu_hour: $5.0000" in summary
    assert "Net Margin per gpu_hour: $5.0000" in summary
    assert "client" in summary  # Per-role breakdown


def test_compute_unit_economics_profit_emoji():
    """Test that summary shows correct emoji for profit."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,
            asset1_amount=10,
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 100.0}
    )

    baseline = BaselineMetrics(
        tx_count=1,
        total_volume_asset0=100.0,
        total_volume_asset1=10.0,
        duration_seconds=86400
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount"
    )

    # Profit case
    result_profit = compute_unit_economics(
        txs, run, baseline, config,
        emissions_usd_per_day=50.0  # < revenue
    )
    summary_profit = result_profit.summary()
    assert "✅" in summary_profit
    assert "PROFIT" in summary_profit

    # Loss case
    result_loss = compute_unit_economics(
        txs, run, baseline, config,
        emissions_usd_per_day=200.0  # > revenue
    )
    summary_loss = result_loss.summary()
    assert "❌" in summary_loss
    assert "LOSS" in summary_loss


def test_compute_unit_economics_invalid_field():
    """Test that invalid resource_amount_field raises error."""
    txs = [
        SentinelTx(
            timestamp=1000,
            user_a=1,
            user_b=2,
            asset0_amount=100,
            asset1_amount=10,
            opcode=Opcode.SWAP,
            role_a="client",
            role_b="miner"
        ),
    ]

    run = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 100.0}
    )

    baseline = BaselineMetrics(
        tx_count=1,
        total_volume_asset0=100.0,
        total_volume_asset1=10.0
    )

    config = UnitEconomicsConfig(
        resource_name="invalid",
        resource_amount_field="invalid_field"
    )

    with pytest.raises(ValueError, match="Unsupported resource_amount_field"):
        compute_unit_economics(txs, run, baseline, config)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
