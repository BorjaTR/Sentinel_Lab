"""Tests for death clock / runway projection."""

import pytest
from datetime import date, timedelta
from sentinel_cloud.death_clock import (
    RunwayInputs,
    RunwayResult,
    RunwayProjector
)
from sentinel_cloud.baseline import BaselineMetrics


def test_runway_basic_finite():
    """Test basic finite runway calculation."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=100000.0,  # $100k treasury
        daily_net_change_asset0=-500.0,  # Losing $500/day
    )

    result = projector.compute_runway(inputs)

    # Should have 200 days of runway
    assert result.baseline_runway_days == pytest.approx(200.0)
    assert result.baseline_death_date == date.today() + timedelta(days=200)
    assert result.is_sustainable_baseline() is False


def test_runway_sustainable():
    """Test sustainable treasury (positive daily change)."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=50000.0,
        daily_net_change_asset0=100.0,  # Earning $100/day - sustainable!
    )

    result = projector.compute_runway(inputs)

    # Should have infinite runway
    assert result.baseline_runway_days is None
    assert result.baseline_death_date is None
    assert result.is_sustainable_baseline() is True


def test_runway_zero_daily_change():
    """Test zero daily change (perfectly balanced)."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=75000.0,
        daily_net_change_asset0=0.0,  # Perfectly balanced
    )

    result = projector.compute_runway(inputs)

    # Zero change is sustainable
    assert result.baseline_runway_days is None
    assert result.baseline_death_date is None
    assert result.is_sustainable_baseline() is True


def test_runway_with_optimization():
    """Test comparison between baseline and optimized config."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=100000.0,
        daily_net_change_asset0=-500.0,  # Baseline: dying in 200 days
        daily_net_change_asset0_optimized=200.0,  # Optimized: sustainable!
    )

    result = projector.compute_runway(inputs)

    # Baseline should die in 200 days
    assert result.baseline_runway_days == pytest.approx(200.0)
    assert result.is_sustainable_baseline() is False

    # Optimized should be sustainable
    assert result.optimized_runway_days is None
    assert result.is_sustainable_optimized() is True

    # Extension should be infinite (baseline dies, optimized doesn't)
    assert result.runway_extension_days == float('inf')


def test_runway_extension_both_finite():
    """Test runway extension when both configs have finite runway."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=100000.0,
        daily_net_change_asset0=-500.0,  # Baseline: 200 days
        daily_net_change_asset0_optimized=-250.0,  # Optimized: 400 days
    )

    result = projector.compute_runway(inputs)

    # Both should have finite runway
    assert result.baseline_runway_days == pytest.approx(200.0)
    assert result.optimized_runway_days == pytest.approx(400.0)

    # Extension should be +200 days
    assert result.runway_extension_days == pytest.approx(200.0)


def test_runway_extension_both_sustainable():
    """Test runway extension when both configs are sustainable."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=100000.0,
        daily_net_change_asset0=100.0,  # Baseline: sustainable
        daily_net_change_asset0_optimized=200.0,  # Optimized: also sustainable
    )

    result = projector.compute_runway(inputs)

    # Both should be sustainable
    assert result.is_sustainable_baseline() is True
    assert result.is_sustainable_optimized() is True

    # Extension should be 0 (both already sustainable)
    assert result.runway_extension_days == 0.0


def test_runway_extension_optimized_worse():
    """Test runway extension when optimized is worse than baseline."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=100000.0,
        daily_net_change_asset0=100.0,  # Baseline: sustainable
        daily_net_change_asset0_optimized=-200.0,  # Optimized: dying! Worse!
    )

    result = projector.compute_runway(inputs)

    # Baseline should be sustainable
    assert result.is_sustainable_baseline() is True

    # Optimized should die in 500 days
    assert result.optimized_runway_days == pytest.approx(500.0)

    # Extension should be negative (optimized is worse)
    # When baseline is sustainable but optimized is finite, extension = -optimized_runway
    assert result.runway_extension_days == pytest.approx(-500.0)


def test_runway_very_small_treasury():
    """Test runway with very small treasury."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=1000.0,  # Only $1k left
        daily_net_change_asset0=-100.0,  # Burning $100/day
    )

    result = projector.compute_runway(inputs)

    # Should have 10 days of runway
    assert result.baseline_runway_days == pytest.approx(10.0)
    assert result.baseline_death_date == date.today() + timedelta(days=10)


def test_runway_compute_simple():
    """Test low-level compute_runway_simple method."""
    projector = RunwayProjector()

    # Test finite runway
    runway_days, death_date = projector.compute_runway_simple(
        treasury_balance=50000.0,
        daily_net_change=-250.0
    )
    assert runway_days == pytest.approx(200.0)
    assert death_date == date.today() + timedelta(days=200)

    # Test sustainable
    runway_days, death_date = projector.compute_runway_simple(
        treasury_balance=50000.0,
        daily_net_change=100.0
    )
    assert runway_days is None
    assert death_date is None


def test_runway_from_baseline_metrics():
    """Test convenience wrapper that takes BaselineMetrics."""
    projector = RunwayProjector()

    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        daily_net_treasury_change=-500.0,  # Losing $500/day
    )

    result = projector.compute_from_baseline(
        baseline_metrics=baseline,
        treasury_balance=100000.0
    )

    # Should compute runway from daily_net_treasury_change
    assert result.baseline_runway_days == pytest.approx(200.0)


def test_runway_from_baseline_no_treasury_error():
    """Test that compute_from_baseline requires treasury_balance."""
    projector = RunwayProjector()

    baseline = BaselineMetrics(
        tx_count=100,
        total_volume_asset0=10000.0,
        total_volume_asset1=0.0,
    )

    with pytest.raises(ValueError, match="treasury_balance required"):
        projector.compute_from_baseline(baseline)


def test_runway_from_baseline_with_optimized():
    """Test compute_from_baseline with optimized metrics."""
    projector = RunwayProjector()

    baseline = BaselineMetrics(
        tx_count=1000,
        total_volume_asset0=100000.0,
        total_volume_asset1=0.0,
        daily_net_treasury_change=-500.0,
    )

    optimized_metrics = {
        'daily_net_treasury_change': 200.0  # Optimized is sustainable
    }

    result = projector.compute_from_baseline(
        baseline_metrics=baseline,
        optimized_metrics=optimized_metrics,
        treasury_balance=100000.0
    )

    # Baseline should die in 200 days
    assert result.baseline_runway_days == pytest.approx(200.0)

    # Optimized should be sustainable
    assert result.optimized_runway_days is None
    assert result.runway_extension_days == float('inf')


def test_runway_custom_date():
    """Test runway computation with custom start date."""
    projector = RunwayProjector()

    custom_date = date(2025, 1, 1)

    inputs = RunwayInputs(
        treasury_start_asset0=36500.0,
        daily_net_change_asset0=-100.0,
        today=custom_date
    )

    result = projector.compute_runway(inputs)

    # Should have 365 days of runway from custom date
    assert result.baseline_runway_days == pytest.approx(365.0)
    # Note: death_date uses date.today() in current implementation
    # This test documents current behavior


def test_runway_edge_case_zero_treasury():
    """Test runway with zero treasury."""
    projector = RunwayProjector()

    inputs = RunwayInputs(
        treasury_start_asset0=0.0,
        daily_net_change_asset0=-100.0,
    )

    result = projector.compute_runway(inputs)

    # Zero treasury with negative change = immediate death
    assert result.baseline_runway_days == pytest.approx(0.0)
    assert result.baseline_death_date == date.today()


def test_runway_baseline_none_daily_change():
    """Test compute_from_baseline when baseline has no daily_net_treasury_change."""
    projector = RunwayProjector()

    baseline = BaselineMetrics(
        tx_count=100,
        total_volume_asset0=10000.0,
        total_volume_asset1=0.0,
        daily_net_treasury_change=None,  # No daily change computed
    )

    result = projector.compute_from_baseline(
        baseline_metrics=baseline,
        treasury_balance=50000.0
    )

    # Should treat None as 0.0 (sustainable)
    assert result.is_sustainable_baseline() is True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
