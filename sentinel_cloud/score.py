"""
Sentinel Score calculation engine.

Calculates a 0-100 sustainability score for crypto protocols.
"""
from dataclasses import dataclass
from typing import Optional
from .protocol_config import ProtocolConfig, RevenueStream


@dataclass
class SentinelScoreResult:
    """Result of Sentinel Score calculation."""
    total_score: int  # 0-100
    grade: str  # S, A, B, C, D, F
    status: str  # Healthy, Warning, Critical

    # Component scores
    runway_score: int  # 0-40
    sustainability_score: int  # 0-30
    diversification_score: int  # 0-20
    trajectory_score: int  # 0-10

    # Key metrics
    runway_months: float
    sustainability_ratio: float

    # Narrative
    summary: str
    recommendations: list[str]

    def to_dict(self) -> dict:
        return {
            'total_score': self.total_score,
            'grade': self.grade,
            'status': self.status,
            'runway_score': self.runway_score,
            'sustainability_score': self.sustainability_score,
            'diversification_score': self.diversification_score,
            'trajectory_score': self.trajectory_score,
            'runway_months': self.runway_months if self.runway_months != float('inf') else None,
            'sustainability_ratio': self.sustainability_ratio if self.sustainability_ratio != float('inf') else None,
            'summary': self.summary,
            'recommendations': self.recommendations,
        }


def calculate_runway_score(runway_months: float) -> int:
    """
    Calculate runway score (0-40 points).

    Crypto-calibrated: 10+ years is effectively infinite in this industry.
    Bitcoin is 15 years old, Ethereum 9 years. Most DAOs are 2-4 years old.

    Args:
        runway_months: Months of runway at current burn rate

    Returns:
        Score from 0-40
    """
    if runway_months == float('inf'):
        return 40  # Profitable protocol
    if runway_months >= 120:  # 10+ years
        return 40  # Effectively infinite in crypto
    elif runway_months >= 60:  # 5-10 years
        return 36  # Very healthy
    elif runway_months >= 36:  # 3-5 years
        return 30  # Healthy
    elif runway_months >= 24:  # 2-3 years
        return 24  # Stable
    elif runway_months >= 12:  # 1-2 years
        return 18  # Caution
    elif runway_months >= 6:  # 6-12 months
        return 10  # Warning
    elif runway_months >= 3:  # 3-6 months
        return 5  # Severe
    else:
        return 0  # <3 months = Critical


def calculate_sustainability_score(sustainability_ratio: float, runway_months: float = 0) -> int:
    """
    Calculate sustainability score (0-30 points).

    Sustainability with runway context: A 0.70 ratio with 300-month runway
    is healthier than a 1.0 ratio with 12-month runway.

    Args:
        sustainability_ratio: monthly_revenue / monthly_costs
        runway_months: Months of runway (for context bonus)

    Returns:
        Score from 0-30
    """
    # Base score from ratio
    if sustainability_ratio >= 1.5:
        base = 30  # Highly profitable
    elif sustainability_ratio >= 1.2:
        base = 27  # Profitable with margin
    elif sustainability_ratio >= 1.0:
        base = 24  # Break-even
    elif sustainability_ratio >= 0.8:
        base = 20  # Slight deficit
    elif sustainability_ratio >= 0.7:
        base = 16  # Manageable deficit
    elif sustainability_ratio >= 0.5:
        base = 10  # Significant deficit
    elif sustainability_ratio >= 0.3:
        base = 5  # Severe deficit
    elif sustainability_ratio > 0:
        base = 2  # Critical but has revenue
    else:
        base = 0  # Zero revenue

    # Runway context bonus (max +8 points)
    # Long runway + decent ratio = significant bonus
    # In crypto, 25 years of runway changes everything
    if runway_months >= 120 and sustainability_ratio >= 0.60:
        base = min(30, base + 8)
    elif runway_months >= 60 and sustainability_ratio >= 0.50:
        base = min(30, base + 4)

    return base


def calculate_revenue_concentration_score(revenue_streams: list[RevenueStream]) -> int:
    """
    Calculate revenue concentration score using HHI (0-10 points).

    Args:
        revenue_streams: List of revenue sources

    Returns:
        Score from 0-10
    """
    if not revenue_streams:
        return 0

    total = sum(s.monthly_usd for s in revenue_streams)
    if total == 0:
        return 0

    # Calculate Herfindahl-Hirschman Index
    shares = [s.monthly_usd / total for s in revenue_streams]
    hhi = sum(s ** 2 for s in shares)

    # Score based on HHI
    if hhi >= 0.9:
        return 0  # Single source dominance
    elif hhi >= 0.7:
        return 2
    elif hhi >= 0.5:
        return 4
    elif hhi >= 0.35:
        return 6
    elif hhi >= 0.25:
        return 8
    else:
        return 10  # Well diversified


def calculate_treasury_concentration_score(treasury) -> int:
    """
    Calculate treasury concentration score (0-10 points).

    Args:
        treasury: Treasury object

    Returns:
        Score from 0-10
    """
    if treasury.balance_usd == 0:
        return 0

    stable_ratio = treasury.stables_ratio

    if stable_ratio >= 0.7:
        return 10  # Mostly stables, low risk
    elif stable_ratio >= 0.5:
        return 8
    elif stable_ratio >= 0.3:
        return 6
    elif stable_ratio >= 0.15:
        return 4
    elif stable_ratio >= 0.05:
        return 2
    else:
        return 0  # Almost entirely native token


def calculate_diversification_score(protocol: ProtocolConfig) -> int:
    """
    Calculate diversification score (0-20 points).

    Args:
        protocol: ProtocolConfig object

    Returns:
        Score from 0-20
    """
    revenue_score = calculate_revenue_concentration_score(protocol.revenue_streams)
    treasury_score = calculate_treasury_concentration_score(protocol.treasury)
    return revenue_score + treasury_score


def calculate_trajectory_score(
    protocol: ProtocolConfig,
) -> int:
    """
    Calculate trajectory score (0-10 points).

    Requires historical data. If not available, returns neutral 5.

    Args:
        protocol: ProtocolConfig with history

    Returns:
        Score from 0-10
    """
    if len(protocol.history) < 2:
        return 5  # Neutral if no historical data

    # Get most recent and 3-month-ago snapshots
    current = protocol.history[-1]
    previous = protocol.history[0] if len(protocol.history) >= 2 else protocol.history[-1]

    current_net = current.monthly_revenue - current.monthly_costs
    previous_net = previous.monthly_revenue - previous.monthly_costs

    # Calculate change
    if previous_net != 0:
        net_change_pct = (current_net - previous_net) / abs(previous_net)
    else:
        net_change_pct = 1.0 if current_net > 0 else -1.0

    # Calculate runway change
    if previous_net < 0:
        prev_runway = previous.treasury_usd / abs(previous_net)
    else:
        prev_runway = float('inf')

    current_runway = protocol.runway_months

    if prev_runway != float('inf') and current_runway != float('inf'):
        runway_change = current_runway - prev_runway
    else:
        runway_change = 0

    # Score based on improvement
    if net_change_pct >= 0.2 and runway_change > 0:
        return 10  # Strong improvement
    elif net_change_pct >= 0.1 or runway_change >= 3:
        return 8  # Moderate improvement
    elif net_change_pct >= 0 or runway_change >= 0:
        return 6  # Stable
    elif net_change_pct >= -0.1 or runway_change >= -3:
        return 4  # Slight decline
    elif net_change_pct >= -0.2:
        return 2  # Moderate decline
    else:
        return 0  # Rapid decline


def score_to_grade(score: int) -> str:
    """
    Convert numeric score to letter grade.

    Crypto-calibrated thresholds:
    - S: Exceptional (profitable + diversified)
    - A: Healthy (long runway + decent sustainability)
    - B: Stable (multi-year runway)
    - C: Caution (needs attention)
    - D: Warning (sustainability issues)
    - F: Critical (immediate risk)
    """
    if score >= 85:
        return "S"
    elif score >= 72:
        return "A"
    elif score >= 58:
        return "B"
    elif score >= 44:
        return "C"
    elif score >= 30:
        return "D"
    else:
        return "F"


def score_to_status(score: int) -> str:
    """
    Convert numeric score to status.

    Crypto-calibrated thresholds aligned with B grade.
    """
    if score >= 58:
        return "Healthy"
    elif score >= 35:
        return "Warning"
    else:
        return "Critical"


def generate_summary(score: int, protocol: ProtocolConfig) -> str:
    """Generate one-line summary of protocol status."""
    runway = protocol.runway_months
    ratio = protocol.sustainability_ratio

    if runway == float('inf'):
        runway_text = "infinite runway (profitable)"
    else:
        runway_text = f"{runway:.1f} months runway"

    if ratio == float('inf'):
        ratio_text = "self-sustaining"
    else:
        ratio_text = f"sustainability ratio at {ratio:.0%}"

    if score >= 72:
        return f"Strong position. {runway_text} with sustainable economics."
    elif score >= 58:
        return f"Healthy. {runway_text}, minor optimizations possible."
    elif score >= 44:
        return f"Caution advised. {runway_text}, {ratio_text}."
    elif score >= 30:
        return f"At risk. {runway_text}. Intervention recommended."
    else:
        return f"Critical. {runway_text} until insolvency without immediate action."


def generate_recommendations(
    protocol: ProtocolConfig,
    r_score: int,
    s_score: int,
    d_score: int,
) -> list[str]:
    """Generate top 3 actionable recommendations."""
    recommendations = []

    # Runway recommendations
    if r_score < 20:
        monthly_deficit = protocol.monthly_burn
        if protocol.sustainability_ratio < 1.0:
            recommendations.append(
                f"Reduce monthly costs by ${monthly_deficit:,.0f} to reach break-even"
            )
        recommendations.append(
            "Consider emergency measures: pause grants, reduce team, or raise capital"
        )

    # Sustainability recommendations
    if s_score < 18 and protocol.cost_streams:
        largest_cost = max(protocol.cost_streams, key=lambda x: x.monthly_usd)
        cost_pct = largest_cost.monthly_usd / protocol.monthly_costs if protocol.monthly_costs > 0 else 0
        recommendations.append(
            f"Review {largest_cost.name}: ${largest_cost.monthly_usd:,.0f}/month "
            f"({cost_pct:.0%} of costs)"
        )

    # Diversification recommendations
    if d_score < 10:
        if protocol.treasury.stables_ratio < 0.3:
            native_pct = 1 - protocol.treasury.stables_ratio
            recommendations.append(
                f"Treasury is {native_pct:.0%} native token. "
                "Consider diversifying to stables."
            )
        if len(protocol.revenue_streams) < 3:
            recommendations.append(
                "Revenue highly concentrated. Explore additional revenue sources."
            )

    return recommendations[:3]  # Top 3 only


def calculate_sentinel_score(protocol: ProtocolConfig) -> SentinelScoreResult:
    """
    Calculate complete Sentinel Score for a protocol.

    Args:
        protocol: ProtocolConfig object

    Returns:
        SentinelScoreResult with score, grade, and recommendations
    """
    # Calculate component scores
    r_score = calculate_runway_score(protocol.runway_months)
    s_score = calculate_sustainability_score(protocol.sustainability_ratio, protocol.runway_months)
    d_score = calculate_diversification_score(protocol)
    t_score = calculate_trajectory_score(protocol)

    # Total score
    total = r_score + s_score + d_score + t_score

    # Derive grade and status
    grade = score_to_grade(total)
    status = score_to_status(total)

    # Generate summary and recommendations
    summary = generate_summary(total, protocol)
    recommendations = generate_recommendations(protocol, r_score, s_score, d_score)

    return SentinelScoreResult(
        total_score=total,
        grade=grade,
        status=status,
        runway_score=r_score,
        sustainability_score=s_score,
        diversification_score=d_score,
        trajectory_score=t_score,
        runway_months=protocol.runway_months,
        sustainability_ratio=protocol.sustainability_ratio,
        summary=summary,
        recommendations=recommendations,
    )
