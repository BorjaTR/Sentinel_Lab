"""Tests for Parameter Safety Scanner."""

import pytest
from sentinel_cloud.safety import (
    SafetyRule,
    SafetyAssessment,
    SafetyScanner
)
from sentinel_cloud.experiment import Config, RunResult
from sentinel_cloud.death_clock import RunwayResult
from sentinel_cloud.baseline import BaselineMetrics


def test_safety_rule_creation():
    """Test creating a safety rule."""
    rule = SafetyRule(
        name="test_rule",
        description="Test rule description",
        check=lambda run, runway, baseline: True,
        severity="warning"
    )

    assert rule.name == "test_rule"
    assert rule.description == "Test rule description"
    assert rule.severity == "warning"
    assert rule.check(None, None, None) is True


def test_safety_rule_invalid_severity():
    """Test that invalid severity raises error."""
    with pytest.raises(ValueError, match="severity must be"):
        SafetyRule(
            name="bad",
            description="Bad",
            check=lambda r, rw, b: True,
            severity="invalid"
        )


def test_safety_assessment_summary():
    """Test SafetyAssessment summary generation."""
    assessment = SafetyAssessment(
        param_name="fee_bps_asset0",
        param_value=50,
        revenue=10000,
        runway_days=200,
        passes={"rule1": True, "rule2": False},
        overall_status="yellow",
        failing_rules=["rule2"]
    )

    summary = assessment.summary()
    assert "fee_bps_asset0=50" in summary
    assert "$10,000/day" in summary
    assert "200 days" in summary
    assert "rule2" in summary
    assert "🟡" in summary


def test_safety_assessment_infinite_runway():
    """Test SafetyAssessment with infinite runway."""
    assessment = SafetyAssessment(
        param_name="fee_bps_asset0",
        param_value=75,
        revenue=15000,
        runway_days=None,  # Sustainable
        passes={"rule1": True},
        overall_status="green"
    )

    summary = assessment.summary()
    assert "∞" in summary
    assert "🟢" in summary


def test_default_rules():
    """Test that default rules are created correctly."""
    scanner = SafetyScanner()

    assert len(scanner.rules) > 0

    # Check that key rules exist
    rule_names = [r.name for r in scanner.rules]
    assert "runway_180d" in rule_names
    assert "failure_rate_1pct" in rule_names
    assert "positive_revenue" in rule_names


def test_assess_config_all_pass():
    """Test assessing a configuration that passes all rules."""
    scanner = SafetyScanner()

    run_result = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={
            'rev_usdc': 10000.0,
            'failure_rate': 0.005  # 0.5% - under threshold
        }
    )

    runway_result = RunwayResult(
        baseline_runway_days=200.0,
        baseline_death_date=None,
        optimized_runway_days=250.0,  # > 180 days
        optimized_death_date=None,
        runway_extension_days=50.0
    )

    assessment = scanner.assess_config(run_result, runway_result)

    assert assessment.overall_status == "green"
    assert len(assessment.failing_rules) == 0
    assert all(assessment.passes.values())


def test_assess_config_critical_failure():
    """Test assessing a configuration that fails critical rule."""
    scanner = SafetyScanner()

    run_result = RunResult(
        config=Config(name="test", fee_bps_asset0=25),
        wall_time_seconds=10.0,
        success=True,
        metrics={
            'rev_usdc': 5000.0,
            'failure_rate': 0.001
        }
    )

    runway_result = RunwayResult(
        baseline_runway_days=200.0,
        baseline_death_date=None,
        optimized_runway_days=100.0,  # < 180 days - CRITICAL FAILURE
        optimized_death_date=None,
        runway_extension_days=-100.0
    )

    assessment = scanner.assess_config(run_result, runway_result)

    assert assessment.overall_status == "red"
    assert "runway_180d" in assessment.failing_rules


def test_assess_config_warning_failure():
    """Test assessing a configuration that fails warning rule."""
    scanner = SafetyScanner()

    run_result = RunResult(
        config=Config(name="test", fee_bps_asset0=100),
        wall_time_seconds=10.0,
        success=True,
        metrics={
            'rev_usdc': 20000.0,
            'failure_rate': 0.02  # 2% - above 1% threshold
        }
    )

    runway_result = RunwayResult(
        baseline_runway_days=200.0,
        baseline_death_date=None,
        optimized_runway_days=300.0,  # Good
        optimized_death_date=None,
        runway_extension_days=100.0
    )

    assessment = scanner.assess_config(run_result, runway_result)

    assert assessment.overall_status == "yellow"
    assert "failure_rate_1pct" in assessment.failing_rules


def test_assess_config_sustainable_runway():
    """Test assessing config with sustainable (infinite) runway."""
    scanner = SafetyScanner()

    run_result = RunResult(
        config=Config(name="test", fee_bps_asset0=75),
        wall_time_seconds=10.0,
        success=True,
        metrics={
            'rev_usdc': 15000.0,
            'failure_rate': 0.001
        }
    )

    runway_result = RunwayResult(
        baseline_runway_days=200.0,
        baseline_death_date=None,
        optimized_runway_days=None,  # Sustainable - should PASS
        optimized_death_date=None,
        runway_extension_days=float('inf')
    )

    assessment = scanner.assess_config(run_result, runway_result)

    assert assessment.overall_status == "green"
    assert assessment.passes.get("runway_180d") is True


def test_assess_config_role_economics():
    """Test role economics safety rule."""
    scanner = SafetyScanner()

    # Config with negative role revenue
    run_result = RunResult(
        config=Config(name="test", fee_bps_asset0=150),
        wall_time_seconds=10.0,
        success=True,
        metrics={
            'rev_usdc': 25000.0,
            'failure_rate': 0.001
        },
        role_metrics={
            'client': {'net_revenue': 5000.0},
            'miner': {'net_revenue': -1000.0}  # Negative!
        }
    )

    runway_result = RunwayResult(
        baseline_runway_days=200.0,
        baseline_death_date=None,
        optimized_runway_days=300.0,
        optimized_death_date=None,
        runway_extension_days=100.0
    )

    assessment = scanner.assess_config(run_result, runway_result)

    assert assessment.overall_status == "yellow"  # Warning, not critical
    assert "no_negative_role_revenue" in assessment.failing_rules


def test_get_safe_range():
    """Test finding safe parameter range."""
    scanner = SafetyScanner()

    assessments = [
        SafetyAssessment("fee", 0, 0, None, {}, "red"),
        SafetyAssessment("fee", 25, 5000, 200, {}, "yellow"),
        SafetyAssessment("fee", 50, 10000, 250, {}, "green"),
        SafetyAssessment("fee", 75, 15000, 300, {}, "green"),
        SafetyAssessment("fee", 100, 20000, 150, {}, "red"),
    ]

    # Green range
    safe_range = scanner.get_safe_range(assessments, "green")
    assert safe_range == (50, 75)

    # Yellow range
    yellow_range = scanner.get_safe_range(assessments, "yellow")
    assert yellow_range == (25, 25)

    # Red range
    red_range = scanner.get_safe_range(assessments, "red")
    assert red_range == (0, 100)


def test_get_safe_range_none():
    """Test get_safe_range when no configs match."""
    scanner = SafetyScanner()

    assessments = [
        SafetyAssessment("fee", 0, 0, None, {}, "red"),
        SafetyAssessment("fee", 100, 20000, 150, {}, "red"),
    ]

    # No green configs
    safe_range = scanner.get_safe_range(assessments, "green")
    assert safe_range is None


def test_summarize():
    """Test summary generation."""
    scanner = SafetyScanner()

    assessments = [
        SafetyAssessment("fee_bps_asset0", 0, 0, 50, {}, "red", ["runway_180d"]),
        SafetyAssessment("fee_bps_asset0", 25, 5000, 200, {}, "yellow", ["failure_rate_1pct"]),
        SafetyAssessment("fee_bps_asset0", 50, 10000, 250, {}, "green", []),
        SafetyAssessment("fee_bps_asset0", 75, 15000, 300, {}, "green", []),
    ]

    summary = scanner.summarize(assessments)

    assert "SAFETY SCAN RESULTS" in summary
    assert "Safe (Green):   2" in summary
    assert "Risky (Yellow): 1" in summary
    assert "Dangerous (Red): 1" in summary
    assert "SAFE RANGE: 50 - 75 bps" in summary


def test_custom_rules():
    """Test scanner with custom rules."""
    # Create custom rule
    custom_rule = SafetyRule(
        name="high_revenue",
        description="Revenue must be > $50k/day",
        check=lambda run, runway, baseline: run.metrics.get('rev_usdc', 0) > 50000,
        severity="critical"
    )

    scanner = SafetyScanner(rules=[custom_rule])

    # Low revenue - should fail
    run_low = RunResult(
        config=Config(name="low", fee_bps_asset0=25),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 10000.0}
    )

    assessment_low = scanner.assess_config(run_low)
    assert assessment_low.overall_status == "red"
    assert "high_revenue" in assessment_low.failing_rules

    # High revenue - should pass
    run_high = RunResult(
        config=Config(name="high", fee_bps_asset0=100),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 75000.0}
    )

    assessment_high = scanner.assess_config(run_high)
    assert assessment_high.overall_status == "green"


def test_check_exception_handling():
    """Test that exceptions in checks are handled gracefully."""
    # Rule that throws exception
    bad_rule = SafetyRule(
        name="bad_rule",
        description="This rule throws",
        check=lambda run, runway, baseline: 1 / 0,  # ZeroDivisionError
        severity="warning"
    )

    scanner = SafetyScanner(rules=[bad_rule])

    run_result = RunResult(
        config=Config(name="test", fee_bps_asset0=50),
        wall_time_seconds=10.0,
        success=True,
        metrics={'rev_usdc': 10000.0}
    )

    assessment = scanner.assess_config(run_result)

    # Should mark as failed, not crash
    assert assessment.passes.get("bad_rule") is False
    assert assessment.overall_status == "yellow"  # Warning failure


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
