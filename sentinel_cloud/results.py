"""
Enhanced result types for programmatic SDK access.

This module provides high-level result types for using Sentinel Cloud
programmatically in notebooks, scripts, and applications.

Usage:
    from sentinel_cloud import SentinelClient

    client = SentinelClient()

    # Quick health check
    quick = client.quick_check("data/scenario.csv", treasury=1_000_000, mapper="solana")
    print(f"Status: {quick.status}")
    print(f"Runway: {quick.runway_days} days")

    # Full analysis
    analysis = client.analyze("data/scenario.csv", treasury=1_000_000, mapper="solana")
    print(f"Safety score: {analysis.safety_score}")
    print(analysis.recommendations)
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Any
from enum import Enum


class HealthStatus(Enum):
    """Health status for protocol treasury."""
    HEALTHY = "healthy"      # Runway > 180 days or sustainable
    WARNING = "warning"      # Runway 90-180 days
    CRITICAL = "critical"    # Runway < 90 days
    EMERGENCY = "emergency"  # Runway < 30 days


@dataclass
class QuickCheckResult:
    """
    Result from quick health check analysis.

    Provides fast assessment of protocol financial health with
    actionable recommendations.

    Attributes:
        status: Health status (healthy/warning/critical/emergency)
        runway_days: Days until treasury depletion (None if sustainable)
        is_sustainable: Whether treasury is self-sustaining
        current_fee_bps: Current fee in basis points
        revenue_per_day: Daily revenue from fees (USDC)
        burn_per_day: Daily emissions/rewards payout (USDC)
        treasury_balance: Current treasury balance (USDC)
        total_volume: Total transaction volume (USDC)
        total_transactions: Number of transactions processed
        suggestions: List of improvement suggestions
        baseline_metrics: Raw baseline metrics from Phase A
        runway_metrics: Raw runway metrics from Phase C
    """
    status: HealthStatus
    runway_days: Optional[float]
    is_sustainable: bool
    current_fee_bps: int
    revenue_per_day: float
    burn_per_day: float
    treasury_balance: float
    total_volume: float
    total_transactions: int
    suggestions: List[str]
    baseline_metrics: Dict[str, Any]
    runway_metrics: Dict[str, Any]

    @property
    def net_daily_flow(self) -> float:
        """Net daily treasury flow (revenue - burn)."""
        return self.revenue_per_day - self.burn_per_day

    @property
    def runway_status(self) -> str:
        """Human-readable runway status."""
        if self.is_sustainable:
            return "♾️ Sustainable"
        elif self.runway_days is None:
            return "Unknown"
        elif self.runway_days < 30:
            return f"💀 EMERGENCY: {self.runway_days:.0f} days"
        elif self.runway_days < 90:
            return f"🔴 CRITICAL: {self.runway_days:.0f} days"
        elif self.runway_days < 180:
            return f"🟡 WARNING: {self.runway_days:.0f} days"
        else:
            return f"✅ HEALTHY: {self.runway_days:.0f} days"

    def print_summary(self):
        """Print formatted summary of quick check results."""
        print("="*70)
        print("Quick Health Check Summary")
        print("="*70)
        print(f"\n📊 Status: {self.status.value.upper()}")
        print(f"🏦 Treasury: ${self.treasury_balance:,.0f}")
        print(f"🛣️  Runway: {self.runway_status}")
        print(f"\n💰 Daily Flows:")
        print(f"   Revenue: ${self.revenue_per_day:>12,.0f}/day")
        print(f"   Burn:    ${self.burn_per_day:>12,.0f}/day")
        print(f"   Net:     ${self.net_daily_flow:>+12,.0f}/day")
        print(f"\n📈 Activity:")
        print(f"   Volume:       ${self.total_volume:,.0f}")
        print(f"   Transactions: {self.total_transactions:,}")
        print(f"   Current fee:  {self.current_fee_bps} bps ({self.current_fee_bps/100:.2f}%)")

        if self.suggestions:
            print(f"\n💡 Suggestions:")
            for i, suggestion in enumerate(self.suggestions, 1):
                print(f"   {i}. {suggestion}")

        print()

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            'status': self.status.value,
            'runway_days': self.runway_days,
            'is_sustainable': self.is_sustainable,
            'current_fee_bps': self.current_fee_bps,
            'revenue_per_day': self.revenue_per_day,
            'burn_per_day': self.burn_per_day,
            'treasury_balance': self.treasury_balance,
            'total_volume': self.total_volume,
            'total_transactions': self.total_transactions,
            'net_daily_flow': self.net_daily_flow,
            'runway_status': self.runway_status,
            'suggestions': self.suggestions,
            'baseline_metrics': self.baseline_metrics,
            'runway_metrics': self.runway_metrics
        }


@dataclass
class AnalysisResult:
    """
    Result from comprehensive 8-phase analysis.

    Provides complete protocol assessment with detailed metrics,
    safety scores, and executive recommendations.

    Attributes:
        scenario_path: Path to scenario data
        mapper: Protocol mapper used
        treasury_balance: Treasury balance (USDC)
        emissions_per_day: Daily emissions rate (optional)

        # Phase results
        baseline: Phase A - Baseline metrics
        comparison: Phase B - Comparison results (if run)
        runway: Phase C - Runway projection
        safety: Phase D - Safety analysis
        unit_economics: Phase E - Unit economics
        concentration: Phase F - Whale/fairness analysis
        governance: Phase G - Governance simulation (if run)
        executive_report: Phase H - Executive summary

        # Aggregate scores
        safety_score: Overall safety score (0-100)
        sustainability_score: Treasury sustainability (0-100)
        risk_level: Aggregate risk level (low/medium/high/critical)

        # Recommendations
        recommendations: List of prioritized recommendations
        critical_issues: List of critical issues requiring immediate action
        warnings: List of warnings
    """
    scenario_path: str
    mapper: str
    treasury_balance: float
    emissions_per_day: Optional[float]

    # Phase results
    baseline: Dict[str, Any]
    comparison: Optional[Dict[str, Any]]
    runway: Dict[str, Any]
    safety: Dict[str, Any]
    unit_economics: Dict[str, Any]
    concentration: Dict[str, Any]
    governance: Optional[Dict[str, Any]]
    executive_report: str

    # Scores
    safety_score: float
    sustainability_score: float
    risk_level: str

    # Recommendations
    recommendations: List[str]
    critical_issues: List[str]
    warnings: List[str]

    def print_summary(self):
        """Print formatted summary of analysis results."""
        print("="*70)
        print("Comprehensive Analysis Summary")
        print("="*70)
        print(f"\nScenario: {self.scenario_path}")
        print(f"Mapper: {self.mapper}")
        print(f"Treasury: ${self.treasury_balance:,.0f}")

        print(f"\n📊 Scores:")
        print(f"   Safety:        {self.safety_score:.1f}/100")
        print(f"   Sustainability: {self.sustainability_score:.1f}/100")
        print(f"   Risk level:     {self.risk_level.upper()}")

        if self.critical_issues:
            print(f"\n🚨 Critical Issues ({len(self.critical_issues)}):")
            for i, issue in enumerate(self.critical_issues, 1):
                print(f"   {i}. {issue}")

        if self.warnings:
            print(f"\n⚠️  Warnings ({len(self.warnings)}):")
            for i, warning in enumerate(self.warnings[:3], 1):
                print(f"   {i}. {warning}")
            if len(self.warnings) > 3:
                print(f"   ... and {len(self.warnings) - 3} more")

        if self.recommendations:
            print(f"\n💡 Recommendations ({len(self.recommendations)}):")
            for i, rec in enumerate(self.recommendations[:5], 1):
                print(f"   {i}. {rec}")
            if len(self.recommendations) > 5:
                print(f"   ... and {len(self.recommendations) - 5} more")

        print(f"\n📄 Executive Report:")
        print("-" * 70)
        print(self.executive_report)
        print()

    def print_phase(self, phase: str):
        """
        Print detailed results for a specific phase.

        Args:
            phase: Phase name ('baseline', 'runway', 'safety', 'unit_economics',
                   'concentration', 'governance', 'comparison')
        """
        phase_data = getattr(self, phase, None)
        if phase_data is None:
            print(f"Phase '{phase}' not available or not run")
            return

        print(f"\n{'='*70}")
        print(f"Phase: {phase.upper()}")
        print('='*70)

        if isinstance(phase_data, dict):
            for key, value in phase_data.items():
                if isinstance(value, float):
                    print(f"{key:30s}: {value:>15,.2f}")
                elif isinstance(value, int):
                    print(f"{key:30s}: {value:>15,}")
                else:
                    print(f"{key:30s}: {value}")
        else:
            print(phase_data)
        print()

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            'scenario_path': self.scenario_path,
            'mapper': self.mapper,
            'treasury_balance': self.treasury_balance,
            'emissions_per_day': self.emissions_per_day,
            'baseline': self.baseline,
            'comparison': self.comparison,
            'runway': self.runway,
            'safety': self.safety,
            'unit_economics': self.unit_economics,
            'concentration': self.concentration,
            'governance': self.governance,
            'executive_report': self.executive_report,
            'safety_score': self.safety_score,
            'sustainability_score': self.sustainability_score,
            'risk_level': self.risk_level,
            'recommendations': self.recommendations,
            'critical_issues': self.critical_issues,
            'warnings': self.warnings
        }
