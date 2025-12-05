"""Tests for before/after comparison engine."""

import pytest
from sentinel_cloud.baseline import BaselineMetrics
from sentinel_cloud.experiment import Config, RunResult
from sentinel_cloud.comparison import ComparisonEngine, ComparisonResult


def test_comparison_basic():
    """Test basic comparison calculation."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=1000.0,  # $1000 baseline revenue
    )

    optimized_run = RunResult(
        config=Config(name="optimized", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 2000.0}  # $2000 optimized revenue
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run, "50 bps")

    assert result.baseline_revenue_asset0 == 1000.0
    assert result.optimized_revenue_asset0 == 2000.0
    assert result.additional_revenue_asset0 == 1000.0
    assert result.pct_improvement_revenue == pytest.approx(100.0)
    assert result.optimized_config_label == "50 bps"


def test_comparison_zero_baseline():
    """Test comparison when baseline revenue is zero."""
    baseline = BaselineMetrics(
        tx_count=100,
        total_volume_asset0=10000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=0.0,  # No baseline revenue
    )

    optimized_run = RunResult(
        config=Config(name="opt", fee_bps_asset0=50),
        wall_time_seconds=5.0,
        success=True,
        metrics={'rev_usdc': 500.0}
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run, "50 bps")

    assert result.additional_revenue_asset0 == 500.0
    assert result.pct_improvement_revenue == 0.0  # Avoid division by zero


def test_comparison_negative_improvement():
    """Test comparison when optimized config is worse than baseline."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=2000.0,  # $2000 baseline
    )

    optimized_run = RunResult(
        config=Config(name="worse", fee_bps_asset0=10),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 1500.0}  # $1500 - worse!
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run, "10 bps")

    assert result.additional_revenue_asset0 == -500.0  # Negative improvement
    assert result.pct_improvement_revenue == pytest.approx(-25.0)


def test_comparison_with_failure_rates():
    """Test comparison including failure rate deltas."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=1000.0,
        failure_rate=0.02,  # 2% baseline failure rate
    )

    optimized_run = RunResult(
        config=Config(name="opt", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={
            'rev_usdc': 2000.0,
            'failure_rate': 0.01  # 1% failure rate - better!
        }
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run, "50 bps")

    assert result.baseline_failure_rate == 0.02
    assert result.optimized_failure_rate == 0.01
    assert result.failure_delta == pytest.approx(-0.01)  # Improved by 1%


def test_comparison_summary():
    """Test summary string generation."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=1000.0,
    )

    optimized_run = RunResult(
        config=Config(name="opt", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 1500.0}
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run, "50 bps (0.50%)")

    summary = result.summary()
    assert "50 bps" in summary
    assert "+$500" in summary  # Additional revenue with formatting
    assert "+50.0%" in summary  # Percentage improvement


def test_find_best_improvement():
    """Test finding best configuration from multiple runs."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=1000.0,
    )

    runs = [
        RunResult(
            config=Config(name="low", fee_bps_asset0=25),
            wall_time_seconds=10.0,
            success=True,
            metrics={'rev_usdc': 1500.0}
        ),
        RunResult(
            config=Config(name="medium", fee_bps_asset0=50),
            wall_time_seconds=10.0,
            success=True,
            metrics={'rev_usdc': 2500.0}  # Best!
        ),
        RunResult(
            config=Config(name="high", fee_bps_asset0=100),
            wall_time_seconds=10.0,
            success=True,
            metrics={'rev_usdc': 2000.0}
        ),
    ]

    engine = ComparisonEngine()
    result = engine.find_best_improvement(baseline, runs)

    # Should pick medium (50 bps) with $2500 revenue
    assert result.optimized_revenue_asset0 == 2500.0
    assert "medium" in result.optimized_config_label or "50" in result.optimized_config_label


def test_find_best_improvement_empty():
    """Test error handling when no runs provided."""
    baseline = BaselineMetrics(
        tx_count=100,
        total_volume_asset0=10000.0,
        total_volume_asset1=0.0,
    )

    engine = ComparisonEngine()

    with pytest.raises(ValueError, match="No simulation results"):
        engine.find_best_improvement(baseline, [])


def test_comparison_alternative_metric_names():
    """Test that comparison handles different revenue metric names."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=1000.0,
    )

    # Test with 'revenue_usdc' instead of 'rev_usdc'
    optimized_run = RunResult(
        config=Config(name="opt", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'revenue_usdc': 2000.0}  # Alternative name
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run)

    assert result.optimized_revenue_asset0 == 2000.0


def test_comparison_baseline_treasury_estimation():
    """Test revenue estimation from treasury change when fees not available."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=None,  # No fees detected
        daily_net_treasury_change=500.0,  # But treasury growing $500/day
        duration_seconds=86400 * 2,  # 2 days
    )

    optimized_run = RunResult(
        config=Config(name="opt", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 2000.0}
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run)

    # Should estimate baseline revenue from treasury change
    # 500/day * 2 days = 1000
    assert result.baseline_revenue_asset0 == pytest.approx(1000.0)


def test_comparison_preserves_references():
    """Test that comparison preserves baseline and optimized references."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=1000.0,
    )

    optimized_run = RunResult(
        config=Config(name="opt", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 2000.0}
    )

    engine = ComparisonEngine()
    result = engine.compare(baseline, optimized_run, "opt")

    # Should preserve original objects
    assert result.baseline is baseline
    assert result.optimized_run is optimized_run
    assert result.is_improvement is True  # 2000 > 1000


def test_is_improvement_flag():
    """Test is_improvement flag for both positive and negative cases."""
    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        total_fees_asset0=2000.0,
    )

    engine = ComparisonEngine()

    # Test improvement case
    good_run = RunResult(
        config=Config(name="good", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 2500.0}  # Better
    )
    good_result = engine.compare(baseline, good_run, "good")
    assert good_result.is_improvement is True
    assert "WORSE" not in good_result.summary()

    # Test worse case
    bad_run = RunResult(
        config=Config(name="bad", fee_bps_asset0=10),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 1500.0}  # Worse
    )
    bad_result = engine.compare(baseline, bad_run, "bad")
    assert bad_result.is_improvement is False
    assert "WORSE" in bad_result.summary()

    # Test equal case (counts as improvement)
    equal_run = RunResult(
        config=Config(name="equal", fee_bps_asset0=40),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 2000.0}  # Equal
    )
    equal_result = engine.compare(baseline, equal_run, "equal")
    assert equal_result.is_improvement is True  # >= baseline


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
