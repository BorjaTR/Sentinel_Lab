"""
Phase H: Executive Report & Narrative Layer

Synthesizes all phases (A-G) into executive-level insights and recommendations.

Answers:
- What's the overall health of this protocol?
- What are the biggest risks?
- What should we do next?
- Is this configuration sustainable?
"""

from dataclasses import dataclass, field
from typing import List, Optional, Dict, Any
from enum import Enum


class RiskLevel(str, Enum):
    """Risk severity levels."""
    CRITICAL = "critical"  # Immediate action required
    HIGH = "high"  # Action needed soon
    MEDIUM = "medium"  # Monitor closely
    LOW = "low"  # Acceptable risk
    NONE = "none"  # No risk identified


class Priority(str, Enum):
    """Recommendation priority levels."""
    IMMEDIATE = "immediate"  # Do this now
    HIGH = "high"  # Do this soon
    MEDIUM = "medium"  # Schedule this
    LOW = "low"  # Nice to have


@dataclass
class Recommendation:
    """
    An actionable recommendation.

    Args:
        title: Short title
        description: Detailed recommendation
        priority: Priority level
        phase: Which phase identified this (e.g., "Phase D: Safety")
        rationale: Why this matters
    """
    title: str
    description: str
    priority: Priority
    phase: str
    rationale: str

    def summary(self) -> str:
        """Generate single-line summary."""
        priority_icons = {
            Priority.IMMEDIATE: "🔴",
            Priority.HIGH: "🟠",
            Priority.MEDIUM: "🟡",
            Priority.LOW: "🟢"
        }
        icon = priority_icons.get(self.priority, "⚪")
        return f"{icon} [{self.priority.value.upper()}] {self.title}"


@dataclass
class ReportSection:
    """
    A section of the executive report.

    Args:
        title: Section title
        status: Overall status (good/warning/critical/unknown)
        summary: Executive summary
        key_findings: List of key findings
        metrics: Dict of key metrics
        risks: List of identified risks
    """
    title: str
    status: str  # "good" | "warning" | "critical" | "unknown"
    summary: str
    key_findings: List[str] = field(default_factory=list)
    metrics: Dict[str, Any] = field(default_factory=dict)
    risks: List[str] = field(default_factory=list)

    def format(self) -> str:
        """Format section for display."""
        status_icons = {
            "good": "🟢",
            "warning": "🟡",
            "critical": "🔴",
            "unknown": "⚪"
        }
        icon = status_icons.get(self.status, "⚪")

        lines = []
        lines.append(f"\n{icon} {self.title}")
        lines.append("─" * 60)
        lines.append(f"{self.summary}")

        if self.key_findings:
            lines.append("\nKey Findings:")
            for finding in self.key_findings:
                lines.append(f"  • {finding}")

        if self.metrics:
            lines.append("\nMetrics:")
            for key, value in self.metrics.items():
                lines.append(f"  {key}: {value}")

        if self.risks:
            lines.append("\n⚠️  Risks:")
            for risk in self.risks:
                lines.append(f"  • {risk}")

        return "\n".join(lines)


@dataclass
class ExecutiveReport:
    """
    Comprehensive executive report synthesizing all phases.

    Args:
        title: Report title
        overall_status: Overall health (good/warning/critical)
        overall_risk: Highest risk level identified
        executive_summary: 2-3 sentence summary
        sections: Report sections from each phase
        recommendations: Prioritized recommendations
        bottom_line: Final verdict
    """
    title: str
    overall_status: str  # "good" | "warning" | "critical"
    overall_risk: RiskLevel
    executive_summary: str
    sections: List[ReportSection] = field(default_factory=list)
    recommendations: List[Recommendation] = field(default_factory=list)
    bottom_line: str = ""

    def format(self) -> str:
        """Generate full executive report."""
        lines = []

        # Header
        lines.append("=" * 60)
        lines.append(f"  {self.title}")
        lines.append("=" * 60)

        # Overall status
        status_icons = {
            "good": "🟢 HEALTHY",
            "warning": "🟡 NEEDS ATTENTION",
            "critical": "🔴 CRITICAL ISSUES"
        }
        status_display = status_icons.get(self.overall_status, "⚪ UNKNOWN")

        risk_icons = {
            RiskLevel.CRITICAL: "🔴 CRITICAL",
            RiskLevel.HIGH: "🟠 HIGH",
            RiskLevel.MEDIUM: "🟡 MEDIUM",
            RiskLevel.LOW: "🟢 LOW",
            RiskLevel.NONE: "✅ NONE"
        }
        risk_display = risk_icons.get(self.overall_risk, "⚪ UNKNOWN")

        lines.append(f"\nOverall Status: {status_display}")
        lines.append(f"Risk Level:     {risk_display}")
        lines.append("")

        # Executive summary
        lines.append("EXECUTIVE SUMMARY")
        lines.append("─" * 60)
        lines.append(self.executive_summary)
        lines.append("")

        # Sections
        for section in self.sections:
            lines.append(section.format())
            lines.append("")

        # Recommendations
        if self.recommendations:
            lines.append("=" * 60)
            lines.append("RECOMMENDATIONS")
            lines.append("=" * 60)

            # Group by priority
            immediate = [r for r in self.recommendations if r.priority == Priority.IMMEDIATE]
            high = [r for r in self.recommendations if r.priority == Priority.HIGH]
            medium = [r for r in self.recommendations if r.priority == Priority.MEDIUM]
            low = [r for r in self.recommendations if r.priority == Priority.LOW]

            for recs, label in [
                (immediate, "Immediate Action Required"),
                (high, "High Priority"),
                (medium, "Medium Priority"),
                (low, "Low Priority")
            ]:
                if recs:
                    lines.append(f"\n{label}:")
                    for rec in recs:
                        lines.append(f"\n  {rec.summary()}")
                        lines.append(f"    {rec.description}")
                        lines.append(f"    Rationale: {rec.rationale}")

        # Bottom line
        if self.bottom_line:
            lines.append("")
            lines.append("=" * 60)
            lines.append("BOTTOM LINE")
            lines.append("=" * 60)
            lines.append(self.bottom_line)

        lines.append("=" * 60)

        return "\n".join(lines)

    def get_immediate_actions(self) -> List[Recommendation]:
        """Get all immediate priority recommendations."""
        return [r for r in self.recommendations if r.priority == Priority.IMMEDIATE]

    def get_critical_risks(self) -> List[str]:
        """Extract all critical risks from sections."""
        risks = []
        for section in self.sections:
            if section.status == "critical":
                risks.extend(section.risks)
        return risks


def generate_executive_report(
    scenario_name: str,
    baseline_metrics: Optional[Dict[str, Any]] = None,
    comparison_results: Optional[Dict[str, Any]] = None,
    runway_results: Optional[Dict[str, Any]] = None,
    safety_assessment: Optional[Dict[str, Any]] = None,
    unit_economics: Optional[Dict[str, Any]] = None,
    concentration_metrics: Optional[Dict[str, Any]] = None,
    governance_results: Optional[Dict[str, Any]] = None
) -> ExecutiveReport:
    """
    Generate comprehensive executive report from all phases.

    Args:
        scenario_name: Name of scenario being analyzed
        baseline_metrics: Phase A - baseline analysis
        comparison_results: Phase B - before/after comparison
        runway_results: Phase C - runway projection
        safety_assessment: Phase D - safety scanner results
        unit_economics: Phase E - unit economics
        concentration_metrics: Phase F - concentration analysis
        governance_results: Phase G - governance simulation

    Returns:
        ExecutiveReport with synthesized insights
    """
    sections = []
    recommendations = []
    overall_risk = RiskLevel.NONE
    overall_status = "good"

    # Phase A: Baseline
    if baseline_metrics:
        revenue = baseline_metrics.get('revenue', 0)
        volume = baseline_metrics.get('volume', 0)
        tx_count = baseline_metrics.get('tx_count', 0)

        baseline_section = ReportSection(
            title="Phase A: Baseline Metrics",
            status="good",
            summary=f"Analyzed {tx_count:,} transactions from mainnet data.",
            key_findings=[
                f"Revenue: ${revenue:,.2f}",
                f"Volume: ${volume:,.2f}",
                f"Transaction count: {tx_count:,}"
            ],
            metrics=baseline_metrics
        )
        sections.append(baseline_section)

    # Phase B: Comparison
    if comparison_results:
        is_improvement = comparison_results.get('is_improvement', False)
        revenue_change_pct = comparison_results.get('revenue_change_pct', 0)

        comparison_status = "good" if is_improvement else "warning"
        comparison_section = ReportSection(
            title="Phase B: Before/After Comparison",
            status=comparison_status,
            summary=f"Configuration changes revenue by {revenue_change_pct:+.1f}%.",
            key_findings=[
                f"Revenue impact: {revenue_change_pct:+.1f}%",
                f"Improvement: {'Yes ✅' if is_improvement else 'No ⚠️'}"
            ],
            metrics=comparison_results
        )
        sections.append(comparison_section)

        if not is_improvement and abs(revenue_change_pct) > 10:
            recommendations.append(Recommendation(
                title="Revenue declining significantly",
                description=f"Configuration reduces revenue by {abs(revenue_change_pct):.1f}%. Consider reverting changes.",
                priority=Priority.HIGH,
                phase="Phase B: Comparison",
                rationale="Double-digit revenue decline indicates suboptimal configuration"
            ))

    # Phase C: Runway
    if runway_results:
        runway_days = runway_results.get('runway_days')
        is_sustainable = runway_results.get('is_sustainable', False)

        if is_sustainable:
            runway_status = "good"
            runway_summary = "Protocol is sustainable - revenue exceeds costs."
        elif runway_days and runway_days > 180:
            runway_status = "good"
            runway_summary = f"Runway: {runway_days:.0f} days (healthy)."
        elif runway_days and runway_days > 90:
            runway_status = "warning"
            runway_summary = f"Runway: {runway_days:.0f} days (monitor closely)."
            overall_status = "warning"
            overall_risk = max_risk(overall_risk, RiskLevel.MEDIUM)
        elif runway_days:
            runway_status = "critical"
            runway_summary = f"Runway: {runway_days:.0f} days (CRITICAL - treasury depleting)."
            overall_status = "critical"
            overall_risk = RiskLevel.CRITICAL
        else:
            runway_status = "unknown"
            runway_summary = "Runway calculation unavailable."

        runway_section = ReportSection(
            title="Phase C: Treasury Runway",
            status=runway_status,
            summary=runway_summary,
            metrics=runway_results
        )

        if runway_status == "critical":
            runway_section.risks = [f"Treasury will be depleted in {runway_days:.0f} days"]
            recommendations.append(Recommendation(
                title="Treasury depletion imminent",
                description=f"Protocol has only {runway_days:.0f} days of runway. Immediate action required.",
                priority=Priority.IMMEDIATE,
                phase="Phase C: Runway",
                rationale="Insufficient runway threatens protocol survival"
            ))

        sections.append(runway_section)

    # Phase D: Safety
    if safety_assessment:
        overall_safety = safety_assessment.get('overall_status', 'unknown')
        failing_rules = safety_assessment.get('failing_rules', [])

        safety_section = ReportSection(
            title="Phase D: Parameter Safety",
            status=overall_safety,
            summary=f"Safety classification: {overall_safety.upper()}.",
            key_findings=[f"Failing rules: {len(failing_rules)}"] if failing_rules else ["All safety checks passed ✅"],
            metrics=safety_assessment
        )

        if overall_safety == "red":
            safety_section.risks = [f"Critical safety violations: {', '.join(failing_rules)}"]
            overall_status = "critical"
            overall_risk = RiskLevel.CRITICAL

            recommendations.append(Recommendation(
                title="Critical safety violations detected",
                description=f"Configuration violates critical safety rules: {', '.join(failing_rules)}.",
                priority=Priority.IMMEDIATE,
                phase="Phase D: Safety",
                rationale="Unsafe configurations can cause protocol failure"
            ))
        elif overall_safety == "yellow":
            safety_section.risks = [f"Safety warnings: {', '.join(failing_rules)}"]
            overall_status = max_status(overall_status, "warning")
            overall_risk = max_risk(overall_risk, RiskLevel.MEDIUM)

        sections.append(safety_section)

    # Phase E: Unit Economics
    if unit_economics:
        net_margin_per_unit = unit_economics.get('net_margin_per_unit', 0)
        profitable = net_margin_per_unit and net_margin_per_unit > 0

        if profitable:
            econ_status = "good"
            econ_summary = f"Unit economics are profitable: ${net_margin_per_unit:.2f} margin per unit."
        elif net_margin_per_unit is not None:
            econ_status = "critical"
            econ_summary = f"Unit economics are negative: ${net_margin_per_unit:.2f} loss per unit."
            overall_status = "critical"
            overall_risk = max_risk(overall_risk, RiskLevel.HIGH)
        else:
            econ_status = "unknown"
            econ_summary = "Unit economics not available."

        econ_section = ReportSection(
            title="Phase E: Unit Economics",
            status=econ_status,
            summary=econ_summary,
            metrics=unit_economics
        )

        if econ_status == "critical":
            econ_section.risks = ["Losing money on every unit sold"]
            recommendations.append(Recommendation(
                title="Negative unit economics",
                description="Protocol loses money on each resource unit. Increase fees or reduce emissions.",
                priority=Priority.IMMEDIATE,
                phase="Phase E: Unit Economics",
                rationale="Negative margins are unsustainable long-term"
            ))

        sections.append(econ_section)

    # Phase F: Concentration
    if concentration_metrics:
        suspicious = concentration_metrics.get('suspicious', False)
        top_10_share = concentration_metrics.get('top_10_share', 0)

        if suspicious:
            conc_status = "warning"
            conc_summary = f"High concentration detected: top 10 control {top_10_share:.1f}% of rewards."
            overall_status = max_status(overall_status, "warning")
            overall_risk = max_risk(overall_risk, RiskLevel.MEDIUM)
        else:
            conc_status = "good"
            conc_summary = f"Reward distribution is reasonable: top 10 have {top_10_share:.1f}%."

        conc_section = ReportSection(
            title="Phase F: Whale & Fairness",
            status=conc_status,
            summary=conc_summary,
            metrics=concentration_metrics
        )

        if suspicious:
            conc_section.risks = ["Reward concentration may indicate centralization"]
            recommendations.append(Recommendation(
                title="High reward concentration",
                description=f"Top 10 users control {top_10_share:.1f}% of rewards. Consider mechanisms to improve distribution.",
                priority=Priority.MEDIUM,
                phase="Phase F: Concentration",
                rationale="Centralization risks protocol decentralization and fairness"
            ))

        sections.append(conc_section)

    # Phase G: Governance
    if governance_results:
        proposal_status = governance_results.get('status', 'unknown')
        whale_controlled = governance_results.get('whale_controlled', False)

        if whale_controlled:
            gov_status = "warning"
            gov_summary = "Governance is whale-controlled: top 10 voters control >50% of power."
            overall_status = max_status(overall_status, "warning")
            overall_risk = max_risk(overall_risk, RiskLevel.MEDIUM)
        else:
            gov_status = "good"
            gov_summary = "Governance power is distributed."

        gov_section = ReportSection(
            title="Phase G: Governance",
            status=gov_status,
            summary=gov_summary,
            key_findings=[f"Proposal status: {proposal_status}"],
            metrics=governance_results
        )

        if whale_controlled:
            gov_section.risks = ["Small group controls governance decisions"]
            recommendations.append(Recommendation(
                title="Governance centralization",
                description="Top 10 voters control majority of voting power. Consider quadratic voting or other mechanisms.",
                priority=Priority.MEDIUM,
                phase="Phase G: Governance",
                rationale="Centralized governance undermines decentralization goals"
            ))

        sections.append(gov_section)

    # Generate executive summary
    exec_summary = _generate_executive_summary(
        scenario_name,
        overall_status,
        overall_risk,
        sections
    )

    # Generate bottom line
    bottom_line = _generate_bottom_line(overall_status, recommendations)

    return ExecutiveReport(
        title=f"Executive Report: {scenario_name}",
        overall_status=overall_status,
        overall_risk=overall_risk,
        executive_summary=exec_summary,
        sections=sections,
        recommendations=recommendations,
        bottom_line=bottom_line
    )


def max_status(status1: str, status2: str) -> str:
    """Return the more severe status."""
    severity = {"good": 0, "warning": 1, "critical": 2, "unknown": -1}
    s1 = severity.get(status1, -1)
    s2 = severity.get(status2, -1)
    if s1 >= s2:
        return status1
    return status2


def max_risk(risk1: RiskLevel, risk2: RiskLevel) -> RiskLevel:
    """Return the higher risk level."""
    severity = {
        RiskLevel.NONE: 0,
        RiskLevel.LOW: 1,
        RiskLevel.MEDIUM: 2,
        RiskLevel.HIGH: 3,
        RiskLevel.CRITICAL: 4
    }
    if severity.get(risk1, 0) >= severity.get(risk2, 0):
        return risk1
    return risk2


def _generate_executive_summary(
    scenario_name: str,
    status: str,
    risk: RiskLevel,
    sections: List[ReportSection]
) -> str:
    """Generate executive summary based on analysis."""
    if status == "critical":
        return (
            f"Analysis of '{scenario_name}' reveals CRITICAL issues requiring immediate attention. "
            f"Protocol sustainability is at risk. Review recommendations below and take action urgently."
        )
    elif status == "warning":
        return (
            f"Analysis of '{scenario_name}' shows concerning trends that need monitoring. "
            f"While not critical, several areas require attention to ensure long-term health."
        )
    else:
        return (
            f"Analysis of '{scenario_name}' shows healthy protocol metrics. "
            f"Configuration appears sustainable with {len(sections)} areas analyzed. Continue monitoring key metrics."
        )


def _generate_bottom_line(status: str, recommendations: List[Recommendation]) -> str:
    """Generate bottom line verdict."""
    immediate = [r for r in recommendations if r.priority == Priority.IMMEDIATE]

    if status == "critical":
        if immediate:
            return f"❌ NOT RECOMMENDED - {len(immediate)} critical issues require immediate action before deployment."
        return "❌ NOT RECOMMENDED - Critical issues detected. Do not proceed with this configuration."
    elif status == "warning":
        if immediate:
            return f"⚠️  PROCEED WITH CAUTION - Address {len(immediate)} immediate issues first."
        return "⚠️  PROCEED WITH CAUTION - Monitor closely and address warnings."
    else:
        return "✅ RECOMMENDED - Configuration appears healthy and sustainable."
