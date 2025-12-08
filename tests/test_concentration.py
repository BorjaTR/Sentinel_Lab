"""Tests for Whale & Fairness Analytics - Concentration Metrics."""

import pytest
from sentinel_cloud.concentration import (
    ConcentrationMetrics,
    compute_gini,
    compute_hhi,
    compute_concentration
)


def test_gini_perfect_equality():
    """Test Gini coefficient with perfect equality."""
    # Everyone has exactly 100
    values = [100, 100, 100, 100, 100]
    gini = compute_gini(values)

    assert gini == pytest.approx(0.0, abs=0.001)


def test_gini_perfect_inequality():
    """Test Gini coefficient with perfect inequality."""
    # One person has almost everything, others have very little
    # (Note: zeros are filtered out, so use small values)
    values = [1, 1, 1, 1, 10000]
    gini = compute_gini(values)

    # With 5 people and 1 having 10000x more, Gini should be very high
    assert gini > 0.7


def test_gini_moderate_inequality():
    """Test Gini coefficient with moderate inequality."""
    # Moderate distribution
    values = [10, 20, 30, 40, 50]
    gini = compute_gini(values)

    # Should be moderate inequality
    assert 0.2 < gini < 0.4


def test_gini_empty_list():
    """Test Gini coefficient with empty list."""
    gini = compute_gini([])
    assert gini == 0.0


def test_gini_single_value():
    """Test Gini coefficient with single value."""
    gini = compute_gini([100])
    assert gini == 0.0  # Single value = perfect equality


def test_gini_all_zeros():
    """Test Gini coefficient with all zeros."""
    gini = compute_gini([0, 0, 0])
    assert gini == 0.0


def test_gini_with_zeros():
    """Test Gini coefficient with some zeros."""
    # Zeros are filtered out
    values = [0, 0, 10, 20, 30]
    gini = compute_gini(values)

    # Should compute on non-zero values only
    assert gini > 0


def test_hhi_perfect_competition():
    """Test HHI with perfect competition (many equal players)."""
    # 10 players with 10% each
    shares = [0.1] * 10
    hhi = compute_hhi(shares)

    # HHI = 10 * (10%)^2 = 10 * 100 = 1000
    assert hhi == pytest.approx(1000.0)


def test_hhi_monopoly():
    """Test HHI with monopoly (one player has 100%)."""
    shares = [1.0]
    hhi = compute_hhi(shares)

    # HHI = (100%)^2 = 10000
    assert hhi == pytest.approx(10000.0)


def test_hhi_duopoly():
    """Test HHI with duopoly (two equal players)."""
    shares = [0.5, 0.5]
    hhi = compute_hhi(shares)

    # HHI = 2 * (50%)^2 = 2 * 2500 = 5000
    assert hhi == pytest.approx(5000.0)


def test_hhi_moderate_concentration():
    """Test HHI with moderate concentration."""
    # 3 players: 50%, 30%, 20%
    shares = [0.5, 0.3, 0.2]
    hhi = compute_hhi(shares)

    # HHI = 50^2 + 30^2 + 20^2 = 2500 + 900 + 400 = 3800
    assert hhi == pytest.approx(3800.0)


def test_hhi_empty_list():
    """Test HHI with empty list."""
    hhi = compute_hhi([])
    assert hhi == 0.0


def test_hhi_with_zeros():
    """Test HHI filters out zeros."""
    shares = [0.0, 0.5, 0.5]
    hhi = compute_hhi(shares)

    # Should compute on non-zero shares only
    assert hhi == pytest.approx(5000.0)


def test_compute_concentration_basic():
    """Test basic concentration computation."""
    rewards = {
        1: 1000,
        2: 500,
        3: 200,
        4: 100,
        5: 50
    }

    metrics = compute_concentration(rewards)

    # Check Gini computed
    assert 0 <= metrics.gini <= 1

    # Check HHI computed
    assert 0 <= metrics.hhi <= 10000

    # Check top-K shares computed
    assert 1 in metrics.top_k_share
    assert 10 in metrics.top_k_share
    assert 100 in metrics.top_k_share

    # Top 1 should have largest share
    assert metrics.top_k_share[1] == 1000 / 1850  # ~54%

    # Top 10 >= all users, should be 100%
    assert metrics.top_k_share[10] == 1.0


def test_compute_concentration_suspicion_gini():
    """Test suspicion flag triggers on high Gini."""
    # Very unequal distribution
    rewards = {i: 1 for i in range(1, 10)}
    rewards[10] = 10000  # One whale

    metrics = compute_concentration(
        rewards,
        gini_threshold=0.6  # Lower threshold
    )

    assert metrics.suspicious is True
    assert any("Gini" in reason for reason in metrics.suspicion_reasons)


def test_compute_concentration_suspicion_top_10():
    """Test suspicion flag triggers on high top-10 share."""
    # Top 10 users dominate
    rewards = {i: 100 for i in range(1, 11)}  # Top 10 with 100 each
    for i in range(11, 101):  # Next 90 with 1 each
        rewards[i] = 1

    metrics = compute_concentration(
        rewards,
        top_10_threshold=0.5
    )

    # Top 10 have 1000, total is 1090, so ~92%
    assert metrics.top_k_share[10] > 0.5
    assert metrics.suspicious is True
    assert any("Top 10" in reason for reason in metrics.suspicion_reasons)


def test_compute_concentration_suspicion_hhi():
    """Test suspicion flag triggers on high HHI."""
    # Highly concentrated - one player dominates
    rewards = {
        1: 9000,
        2: 500,
        3: 300,
        4: 200
    }

    metrics = compute_concentration(
        rewards,
        hhi_threshold=2000  # Lower threshold
    )

    assert metrics.suspicious is True
    assert any("HHI" in reason for reason in metrics.suspicion_reasons)


def test_compute_concentration_not_suspicious():
    """Test that well-distributed rewards don't trigger suspicion."""
    # 100 users with roughly equal rewards
    rewards = {i: 100 + (i % 20) for i in range(1, 101)}

    metrics = compute_concentration(rewards)

    assert metrics.suspicious is False
    assert len(metrics.suspicion_reasons) == 0


def test_compute_concentration_empty_rewards():
    """Test concentration with no rewards."""
    metrics = compute_concentration({})

    assert metrics.gini == 0.0
    assert metrics.hhi == 0.0
    assert metrics.top_k_share[1] == 0.0
    assert metrics.top_k_share[10] == 0.0
    assert metrics.suspicious is False


def test_compute_concentration_single_user():
    """Test concentration with single user."""
    rewards = {1: 1000}

    metrics = compute_concentration(rewards)

    # Single user = perfect equality (Gini = 0)
    assert metrics.gini == 0.0
    # Single user = monopoly (HHI = 10000)
    assert metrics.hhi == pytest.approx(10000.0)
    # Top-K all = 100%
    assert metrics.top_k_share[1] == 1.0
    assert metrics.top_k_share[10] == 1.0


def test_compute_concentration_top_k_ordering():
    """Test top-K shares are computed correctly."""
    rewards = {i: 100 - i for i in range(1, 21)}  # 99, 98, 97, ..., 80

    metrics = compute_concentration(rewards, top_k_values=[1, 5, 10, 20])

    total = sum(rewards.values())

    # Top 1 = 99
    assert metrics.top_k_share[1] == pytest.approx(99 / total)

    # Top 5 = 99 + 98 + 97 + 96 + 95
    top_5_sum = sum(100 - i for i in range(1, 6))
    assert metrics.top_k_share[5] == pytest.approx(top_5_sum / total)

    # Top 20 = everyone
    assert metrics.top_k_share[20] == 1.0


def test_compute_concentration_zero_rewards():
    """Test concentration filters out zero rewards."""
    rewards = {
        1: 1000,
        2: 0,
        3: 500,
        4: 0,
        5: 200
    }

    metrics = compute_concentration(rewards)

    # Should compute on non-zero values only
    assert metrics.gini > 0
    total = 1700
    assert metrics.top_k_share[1] == pytest.approx(1000 / total)


def test_concentration_metrics_summary():
    """Test ConcentrationMetrics summary generation."""
    metrics = ConcentrationMetrics(
        gini=0.85,
        hhi=3500,
        top_k_share={1: 0.45, 10: 0.72, 100: 0.95},
        suspicious=True,
        suspicion_reasons=["High Gini coefficient (0.850 > 0.7)"]
    )

    summary = metrics.summary()

    # Check key elements present
    assert "WHALE & FAIRNESS ANALYSIS" in summary
    assert "Gini Coefficient: 0.850" in summary
    assert "HHI Index: 3500" in summary
    assert "Top   1 users:" in summary
    assert "Top  10 users:" in summary
    assert "Top 100 users:" in summary
    assert "CONCENTRATION WARNING" in summary
    assert "High Gini coefficient" in summary


def test_concentration_metrics_summary_not_suspicious():
    """Test summary when not suspicious."""
    metrics = ConcentrationMetrics(
        gini=0.3,
        hhi=1200,
        top_k_share={1: 0.05, 10: 0.25, 100: 0.80},
        suspicious=False,
        suspicion_reasons=[]
    )

    summary = metrics.summary()

    assert "Distribution appears reasonable" in summary
    assert "CONCENTRATION WARNING" not in summary


def test_concentration_metrics_summary_emojis():
    """Test that summary uses correct emoji indicators."""
    # Low inequality
    metrics_low = ConcentrationMetrics(
        gini=0.2, hhi=800, top_k_share={10: 0.3},
        suspicious=False
    )
    summary_low = metrics_low.summary()
    assert "✅" in summary_low

    # High inequality
    metrics_high = ConcentrationMetrics(
        gini=0.75, hhi=3000, top_k_share={10: 0.8},
        suspicious=True
    )
    summary_high = metrics_high.summary()
    assert "🔴" in summary_high


def test_compute_concentration_custom_thresholds():
    """Test custom threshold configuration."""
    rewards = {i: 100 for i in range(1, 11)}

    # Very strict thresholds
    metrics_strict = compute_concentration(
        rewards,
        gini_threshold=0.1,
        top_10_threshold=0.5,
        hhi_threshold=500
    )

    # Should trigger suspicion even with equal distribution
    # because HHI = 10 * 10^2 = 1000 > 500
    assert metrics_strict.suspicious is True


def test_compute_concentration_large_user_base():
    """Test concentration with large user base."""
    # 1000 users with power-law distribution
    rewards = {i: 1000 / (i ** 0.5) for i in range(1, 1001)}

    metrics = compute_concentration(rewards, top_k_values=[1, 10, 100, 1000])

    # Top 1 should have significant but not dominant share
    assert 0.01 < metrics.top_k_share[1] < 0.2

    # Top 100 should have significant share
    assert metrics.top_k_share[100] > 0.2

    # Top 1000 = everyone
    assert metrics.top_k_share[1000] == 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
