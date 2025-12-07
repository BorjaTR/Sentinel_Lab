"""Tests for Executive Report & Narrative Layer."""

import pytest
from sentinel_cloud.executive_report import (
    RiskLevel,
    Priority,
    Recommendation,
    ReportSection,
    ExecutiveReport,
    generate_executive_report,
    max_status
)


def test_recommendation_creation():
    """Test Recommendation creation."""
    rec = Recommendation(
        title="Fix critical issue",
        description="This needs immediate attention",
        priority=Priority.IMMEDIATE,
        phase="Phase D: Safety",
        rationale="Protocol stability at risk"
    )

    assert rec.title == "Fix critical issue"
    assert rec.priority == Priority.IMMEDIATE
    assert rec.phase == "Phase D: Safety"


def test_recommendation_summary():
    """Test Recommendation.summary() formatting."""
    rec = Recommendation(
        title="Increase fees",
        description="Raise transaction fees",
        priority=Priority.HIGH,
        phase="Phase E",
        rationale="Improve economics"
    )

    summary = rec.summary()

    assert "HIGH" in summary
    assert "Increase fees" in summary
    assert "🟠" in summary  # High priority icon


def test_recommendation_priority_icons():
    """Test all priority icons in summaries."""
    priorities = [
        (Priority.IMMEDIATE, "🔴"),
        (Priority.HIGH, "🟠"),
        (Priority.MEDIUM, "🟡"),
        (Priority.LOW, "🟢")
    ]

    for priority, expected_icon in priorities:
        rec = Recommendation("Test", "Desc", priority, "Phase", "Rationale")
        assert expected_icon in rec.summary()


def test_report_section_creation():
    """Test ReportSection creation."""
    section = ReportSection(
        title="Baseline Metrics",
        status="good",
        summary="All metrics look healthy",
        key_findings=["Revenue: $100K", "Volume: $500K"],
        metrics={"revenue": 100000, "volume": 500000},
        risks=[]
    )

    assert section.title == "Baseline Metrics"
    assert section.status == "good"
    assert len(section.key_findings) == 2
    assert section.metrics["revenue"] == 100000


def test_report_section_format():
    """Test ReportSection.format() output."""
    section = ReportSection(
        title="Test Section",
        status="warning",
        summary="Some issues detected",
        key_findings=["Finding 1", "Finding 2"],
        metrics={"metric1": 100},
        risks=["Risk 1"]
    )

    formatted = section.format()

    assert "Test Section" in formatted
    assert "🟡" in formatted  # Warning icon
    assert "Some issues detected" in formatted
    assert "Finding 1" in formatted
    assert "metric1" in formatted
    assert "Risk 1" in formatted


def test_report_section_status_icons():
    """Test all status icons in section format."""
    statuses = [
        ("good", "🟢"),
        ("warning", "🟡"),
        ("critical", "🔴"),
        ("unknown", "⚪")
    ]

    for status, expected_icon in statuses:
        section = ReportSection(status, status, f"Status: {status}")
        assert expected_icon in section.format()


def test_executive_report_creation():
    """Test ExecutiveReport creation."""
    report = ExecutiveReport(
        title="Test Report",
        overall_status="good",
        overall_risk=RiskLevel.LOW,
        executive_summary="Everything is fine",
        sections=[],
        recommendations=[],
        bottom_line="✅ RECOMMENDED"
    )

    assert report.title == "Test Report"
    assert report.overall_status == "good"
    assert report.overall_risk == RiskLevel.LOW


def test_executive_report_format():
    """Test ExecutiveReport.format() output."""
    section = ReportSection(
        "Phase A",
        "good",
        "Baseline looks good"
    )

    rec = Recommendation(
        "Do this",
        "Important action",
        Priority.HIGH,
        "Phase D",
        "Because reasons"
    )

    report = ExecutiveReport(
        title="Test Report",
        overall_status="good",
        overall_risk=RiskLevel.LOW,
        executive_summary="All systems operational",
        sections=[section],
        recommendations=[rec],
        bottom_line="✅ RECOMMENDED"
    )

    formatted = report.format()

    assert "Test Report" in formatted
    assert "🟢 HEALTHY" in formatted
    assert "🟢 LOW" in formatted
    assert "EXECUTIVE SUMMARY" in formatted
    assert "All systems operational" in formatted
    assert "Phase A" in formatted
    assert "RECOMMENDATIONS" in formatted
    assert "Do this" in formatted
    assert "BOTTOM LINE" in formatted
    assert "✅ RECOMMENDED" in formatted


def test_executive_report_get_immediate_actions():
    """Test getting immediate priority recommendations."""
    recs = [
        Recommendation("A", "Desc", Priority.IMMEDIATE, "P", "R"),
        Recommendation("B", "Desc", Priority.HIGH, "P", "R"),
        Recommendation("C", "Desc", Priority.IMMEDIATE, "P", "R"),
        Recommendation("D", "Desc", Priority.LOW, "P", "R")
    ]

    report = ExecutiveReport(
        "Test",
        "good",
        RiskLevel.LOW,
        "Summary",
        recommendations=recs
    )

    immediate = report.get_immediate_actions()

    assert len(immediate) == 2
    assert all(r.priority == Priority.IMMEDIATE for r in immediate)


def test_executive_report_get_critical_risks():
    """Test extracting critical risks from sections."""
    sections = [
        ReportSection("S1", "good", "OK", risks=[]),
        ReportSection("S2", "critical", "Bad", risks=["Risk 1", "Risk 2"]),
        ReportSection("S3", "warning", "Meh", risks=["Risk 3"]),
        ReportSection("S4", "critical", "Bad", risks=["Risk 4"])
    ]

    report = ExecutiveReport(
        "Test",
        "critical",
        RiskLevel.CRITICAL,
        "Summary",
        sections=sections
    )

    risks = report.get_critical_risks()

    # Should only get risks from critical sections
    assert len(risks) == 3
    assert "Risk 1" in risks
    assert "Risk 2" in risks
    assert "Risk 4" in risks
    assert "Risk 3" not in risks  # Warning section


def test_generate_executive_report_baseline_only():
    """Test report generation with only baseline metrics."""
    baseline = {
        'revenue': 100000,
        'volume': 500000,
        'tx_count': 1000
    }

    report = generate_executive_report(
        "Test Scenario",
        baseline_metrics=baseline
    )

    assert report.title == "Executive Report: Test Scenario"
    assert report.overall_status == "good"
    assert report.overall_risk == RiskLevel.NONE
    assert len(report.sections) == 1
    assert "Phase A" in report.sections[0].title


def test_generate_executive_report_critical_runway():
    """Test report detects critical runway issues."""
    runway = {
        'runway_days': 30,
        'is_sustainable': False
    }

    report = generate_executive_report(
        "Test",
        runway_results=runway
    )

    assert report.overall_status == "critical"
    assert report.overall_risk == RiskLevel.CRITICAL
    assert len(report.sections) == 1
    assert report.sections[0].status == "critical"
    assert len(report.recommendations) > 0
    assert any(r.priority == Priority.IMMEDIATE for r in report.recommendations)


def test_generate_executive_report_sustainable_runway():
    """Test report recognizes sustainable protocol."""
    runway = {
        'runway_days': None,
        'is_sustainable': True
    }

    report = generate_executive_report(
        "Test",
        runway_results=runway
    )

    assert report.overall_status == "good"
    assert report.sections[0].status == "good"
    assert "sustainable" in report.sections[0].summary.lower()


def test_generate_executive_report_safety_red():
    """Test report detects critical safety violations."""
    safety = {
        'overall_status': 'red',
        'failing_rules': ['runway_180d', 'positive_revenue']
    }

    report = generate_executive_report(
        "Test",
        safety_assessment=safety
    )

    assert report.overall_status == "critical"
    assert report.overall_risk == RiskLevel.CRITICAL
    assert any("safety" in r.title.lower() for r in report.recommendations)


def test_generate_executive_report_safety_yellow():
    """Test report detects safety warnings."""
    safety = {
        'overall_status': 'yellow',
        'failing_rules': ['failure_rate_1pct']
    }

    report = generate_executive_report(
        "Test",
        safety_assessment=safety
    )

    assert report.overall_status == "warning"
    assert report.overall_risk == RiskLevel.MEDIUM


def test_generate_executive_report_safety_green():
    """Test report recognizes safe configuration."""
    safety = {
        'overall_status': 'green',
        'failing_rules': []
    }

    report = generate_executive_report(
        "Test",
        safety_assessment=safety
    )

    assert report.overall_status == "good"
    assert report.sections[0].status == "green"


def test_generate_executive_report_negative_unit_economics():
    """Test report detects negative unit economics."""
    unit_econ = {
        'net_margin_per_unit': -5.0,
        'revenue_per_unit': 10.0,
        'emissions_per_unit': 15.0
    }

    report = generate_executive_report(
        "Test",
        unit_economics=unit_econ
    )

    assert report.overall_status == "critical"
    assert report.overall_risk == RiskLevel.HIGH
    assert report.sections[0].status == "critical"
    assert any("negative" in r.title.lower() for r in report.recommendations)


def test_generate_executive_report_positive_unit_economics():
    """Test report recognizes profitable unit economics."""
    unit_econ = {
        'net_margin_per_unit': 5.0,
        'revenue_per_unit': 15.0,
        'emissions_per_unit': 10.0
    }

    report = generate_executive_report(
        "Test",
        unit_economics=unit_econ
    )

    assert report.sections[0].status == "good"
    assert "profitable" in report.sections[0].summary.lower()


def test_generate_executive_report_high_concentration():
    """Test report detects whale concentration."""
    concentration = {
        'suspicious': True,
        'top_10_share': 75.0,
        'gini': 0.85
    }

    report = generate_executive_report(
        "Test",
        concentration_metrics=concentration
    )

    assert report.overall_status == "warning"
    assert report.overall_risk == RiskLevel.MEDIUM
    assert report.sections[0].status == "warning"
    assert any("concentration" in r.title.lower() for r in report.recommendations)


def test_generate_executive_report_low_concentration():
    """Test report recognizes good distribution."""
    concentration = {
        'suspicious': False,
        'top_10_share': 15.0,
        'gini': 0.3
    }

    report = generate_executive_report(
        "Test",
        concentration_metrics=concentration
    )

    assert report.sections[0].status == "good"


def test_generate_executive_report_whale_governance():
    """Test report detects governance centralization."""
    governance = {
        'status': 'passed',
        'whale_controlled': True,
        'top_10_share': 65.0
    }

    report = generate_executive_report(
        "Test",
        governance_results=governance
    )

    assert report.overall_status == "warning"
    assert report.overall_risk == RiskLevel.MEDIUM
    assert report.sections[0].status == "warning"
    assert any("governance" in r.title.lower() for r in report.recommendations)


def test_generate_executive_report_distributed_governance():
    """Test report recognizes distributed governance."""
    governance = {
        'status': 'passed',
        'whale_controlled': False,
        'top_10_share': 20.0
    }

    report = generate_executive_report(
        "Test",
        governance_results=governance
    )

    assert report.sections[0].status == "good"


def test_generate_executive_report_revenue_decline():
    """Test report detects significant revenue decline."""
    comparison = {
        'is_improvement': False,
        'revenue_change_pct': -15.0
    }

    report = generate_executive_report(
        "Test",
        comparison_results=comparison
    )

    # Should have a recommendation
    assert len(report.recommendations) > 0
    assert any("revenue" in r.title.lower() for r in report.recommendations)


def test_generate_executive_report_revenue_improvement():
    """Test report recognizes revenue improvement."""
    comparison = {
        'is_improvement': True,
        'revenue_change_pct': 25.0
    }

    report = generate_executive_report(
        "Test",
        comparison_results=comparison
    )

    assert report.sections[0].status == "good"


def test_generate_executive_report_all_phases():
    """Test report generation with all phases."""
    report = generate_executive_report(
        "Complete Analysis",
        baseline_metrics={'revenue': 100000, 'volume': 500000, 'tx_count': 1000},
        comparison_results={'is_improvement': True, 'revenue_change_pct': 10.0},
        runway_results={'runway_days': 365, 'is_sustainable': False},
        safety_assessment={'overall_status': 'green', 'failing_rules': []},
        unit_economics={'net_margin_per_unit': 2.5},
        concentration_metrics={'suspicious': False, 'top_10_share': 20.0},
        governance_results={'status': 'passed', 'whale_controlled': False}
    )

    # Should have 7 sections (one per phase)
    assert len(report.sections) == 7
    assert report.overall_status == "good"
    assert report.overall_risk == RiskLevel.NONE


def test_generate_executive_report_multiple_critical_issues():
    """Test report with multiple critical issues."""
    report = generate_executive_report(
        "Crisis Scenario",
        runway_results={'runway_days': 15, 'is_sustainable': False},
        safety_assessment={'overall_status': 'red', 'failing_rules': ['runway_180d']},
        unit_economics={'net_margin_per_unit': -10.0}
    )

    assert report.overall_status == "critical"
    assert report.overall_risk == RiskLevel.CRITICAL
    assert len(report.get_immediate_actions()) >= 2
    assert "NOT RECOMMENDED" in report.bottom_line


def test_generate_executive_report_bottom_line_critical():
    """Test bottom line for critical status."""
    report = generate_executive_report(
        "Test",
        runway_results={'runway_days': 20, 'is_sustainable': False}
    )

    assert "NOT RECOMMENDED" in report.bottom_line
    assert "❌" in report.bottom_line


def test_generate_executive_report_bottom_line_warning():
    """Test bottom line for warning status."""
    report = generate_executive_report(
        "Test",
        concentration_metrics={'suspicious': True, 'top_10_share': 70.0}
    )

    assert "PROCEED WITH CAUTION" in report.bottom_line
    assert "⚠️" in report.bottom_line


def test_generate_executive_report_bottom_line_good():
    """Test bottom line for good status."""
    report = generate_executive_report(
        "Test",
        baseline_metrics={'revenue': 100000, 'volume': 500000, 'tx_count': 1000}
    )

    assert "RECOMMENDED" in report.bottom_line
    assert "✅" in report.bottom_line


def test_max_status():
    """Test max_status utility function."""
    assert max_status("good", "good") == "good"
    assert max_status("good", "warning") == "warning"
    assert max_status("warning", "good") == "warning"
    assert max_status("warning", "critical") == "critical"
    assert max_status("critical", "good") == "critical"
    assert max_status("critical", "critical") == "critical"


def test_max_status_with_unknown():
    """Test max_status handles unknown."""
    assert max_status("good", "unknown") == "good"
    assert max_status("unknown", "warning") == "warning"
    assert max_status("unknown", "unknown") == "unknown"


def test_executive_summary_critical():
    """Test executive summary for critical status."""
    report = generate_executive_report(
        "Critical Test",
        runway_results={'runway_days': 10, 'is_sustainable': False}
    )

    assert "CRITICAL" in report.executive_summary.upper()
    assert "immediate" in report.executive_summary.lower()


def test_executive_summary_warning():
    """Test executive summary for warning status."""
    report = generate_executive_report(
        "Warning Test",
        concentration_metrics={'suspicious': True, 'top_10_share': 65.0}
    )

    assert "concerning" in report.executive_summary.lower() or "attention" in report.executive_summary.lower()


def test_executive_summary_good():
    """Test executive summary for good status."""
    report = generate_executive_report(
        "Good Test",
        baseline_metrics={'revenue': 100000, 'volume': 500000, 'tx_count': 1000}
    )

    assert "healthy" in report.executive_summary.lower() or "sustainable" in report.executive_summary.lower()


def test_report_recommendation_grouping():
    """Test that recommendations are grouped by priority in format."""
    recs = [
        Recommendation("Low 1", "D", Priority.LOW, "P", "R"),
        Recommendation("Immediate 1", "D", Priority.IMMEDIATE, "P", "R"),
        Recommendation("High 1", "D", Priority.HIGH, "P", "R"),
        Recommendation("Medium 1", "D", Priority.MEDIUM, "P", "R"),
        Recommendation("Immediate 2", "D", Priority.IMMEDIATE, "P", "R")
    ]

    report = ExecutiveReport(
        "Test",
        "warning",
        RiskLevel.MEDIUM,
        "Summary",
        recommendations=recs
    )

    formatted = report.format()

    # Check that priority sections appear in order
    immediate_pos = formatted.find("Immediate Action Required")
    high_pos = formatted.find("High Priority")
    medium_pos = formatted.find("Medium Priority")
    low_pos = formatted.find("Low Priority")

    assert immediate_pos < high_pos < medium_pos < low_pos


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
