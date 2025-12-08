"""
Proposal impact analyzer for Sentinel.

Simulates governance proposals and shows impact on Sentinel Score.
"""
from dataclasses import dataclass
from typing import Literal, Optional
from copy import deepcopy

from .protocol_config import ProtocolConfig, RevenueStream, CostStream
from .score import calculate_sentinel_score, SentinelScoreResult


@dataclass
class ProposalChange:
    """A proposed change to protocol parameters."""
    action: Literal["add", "remove", "modify"]
    stream_type: Literal["revenue", "cost"]
    stream_name: str
    new_value: Optional[float] = None
    description: str = ""
    is_discretionary: bool = False


@dataclass
class ProposalImpactResult:
    """Result of proposal impact analysis."""
    before_score: SentinelScoreResult
    after_score: SentinelScoreResult
    score_change: int
    runway_change_months: float
    sustainability_change: float

    # Analysis
    warnings: list[str]
    recommendations: list[str]
    alternatives: list[str]

    def to_dict(self) -> dict:
        return {
            'before': self.before_score.to_dict(),
            'after': self.after_score.to_dict(),
            'changes': {
                'score': self.score_change,
                'runway_months': self.runway_change_months if self.runway_change_months != float('inf') else None,
                'sustainability_ratio': self.sustainability_change if self.sustainability_change != float('inf') else None,
            },
            'warnings': self.warnings,
            'recommendations': self.recommendations,
            'alternatives': self.alternatives,
        }


def apply_proposal_changes(
    protocol: ProtocolConfig,
    changes: list[ProposalChange]
) -> ProtocolConfig:
    """
    Apply proposed changes to a protocol config.

    Args:
        protocol: Base protocol config
        changes: List of proposed changes

    Returns:
        New ProtocolConfig with changes applied
    """
    # Deep copy to avoid mutating original
    new_protocol = deepcopy(protocol)

    for change in changes:
        if change.stream_type == "revenue":
            _apply_revenue_change(new_protocol, change)
        elif change.stream_type == "cost":
            _apply_cost_change(new_protocol, change)

    return new_protocol


def _apply_revenue_change(protocol: ProtocolConfig, change: ProposalChange):
    """Apply a revenue stream change."""
    if change.action == "add":
        protocol.revenue_streams.append(
            RevenueStream(
                name=change.stream_name,
                monthly_usd=change.new_value or 0,
                description=change.description,
            )
        )
    elif change.action == "remove":
        protocol.revenue_streams = [
            s for s in protocol.revenue_streams
            if s.name != change.stream_name
        ]
    elif change.action == "modify":
        for stream in protocol.revenue_streams:
            if stream.name == change.stream_name:
                if change.new_value is not None:
                    stream.monthly_usd = change.new_value
                if change.description:
                    stream.description = change.description


def _apply_cost_change(protocol: ProtocolConfig, change: ProposalChange):
    """Apply a cost stream change."""
    if change.action == "add":
        protocol.cost_streams.append(
            CostStream(
                name=change.stream_name,
                monthly_usd=change.new_value or 0,
                description=change.description,
                is_discretionary=change.is_discretionary,
            )
        )
    elif change.action == "remove":
        protocol.cost_streams = [
            s for s in protocol.cost_streams
            if s.name != change.stream_name
        ]
    elif change.action == "modify":
        for stream in protocol.cost_streams:
            if stream.name == change.stream_name:
                if change.new_value is not None:
                    stream.monthly_usd = change.new_value
                if change.description:
                    stream.description = change.description


def analyze_proposal_impact(
    protocol: ProtocolConfig,
    changes: list[ProposalChange]
) -> ProposalImpactResult:
    """
    Analyze the impact of proposed changes on Sentinel Score.

    Args:
        protocol: Base protocol config
        changes: List of proposed changes

    Returns:
        ProposalImpactResult with before/after analysis
    """
    # Calculate before state
    before_score = calculate_sentinel_score(protocol)

    # Apply changes and calculate after state
    after_protocol = apply_proposal_changes(protocol, changes)
    after_score = calculate_sentinel_score(after_protocol)

    # Calculate deltas
    score_change = after_score.total_score - before_score.total_score

    if before_score.runway_months == float('inf') and after_score.runway_months == float('inf'):
        runway_change = 0
    elif before_score.runway_months == float('inf'):
        runway_change = -after_score.runway_months
    elif after_score.runway_months == float('inf'):
        runway_change = float('inf')
    else:
        runway_change = after_score.runway_months - before_score.runway_months

    if before_score.sustainability_ratio == float('inf') and after_score.sustainability_ratio == float('inf'):
        sustainability_change = 0
    elif before_score.sustainability_ratio == float('inf'):
        sustainability_change = -after_score.sustainability_ratio
    elif after_score.sustainability_ratio == float('inf'):
        sustainability_change = float('inf')
    else:
        sustainability_change = after_score.sustainability_ratio - before_score.sustainability_ratio

    # Generate warnings and recommendations
    warnings = _generate_warnings(before_score, after_score, score_change, runway_change)
    recommendations = _generate_proposal_recommendations(protocol, after_protocol, changes)
    alternatives = _generate_alternatives(protocol, changes, score_change)

    return ProposalImpactResult(
        before_score=before_score,
        after_score=after_score,
        score_change=score_change,
        runway_change_months=runway_change,
        sustainability_change=sustainability_change,
        warnings=warnings,
        recommendations=recommendations,
        alternatives=alternatives,
    )


def _generate_warnings(
    before: SentinelScoreResult,
    after: SentinelScoreResult,
    score_change: int,
    runway_change: float
) -> list[str]:
    """Generate warnings about proposal impact."""
    warnings = []

    if score_change < -10:
        warnings.append(f"⚠️  Score drops significantly ({score_change} points)")

    if runway_change < -6 and runway_change != float('inf'):
        warnings.append(f"⚠️  Runway decreases by {abs(runway_change):.1f} months")

    if before.status == "Healthy" and after.status == "Warning":
        warnings.append("⚠️  Status downgrades from Healthy to Warning")

    if before.status in ["Healthy", "Warning"] and after.status == "Critical":
        warnings.append("🚨 Status downgrades to Critical")

    if after.runway_months < 6 and after.runway_months != float('inf'):
        warnings.append(f"🚨 Runway falls below 6 months ({after.runway_months:.1f} months)")

    if after.sustainability_ratio < 0.5:
        warnings.append(f"⚠️  Sustainability ratio falls to {after.sustainability_ratio:.0%}")

    return warnings


def _generate_proposal_recommendations(
    before: ProtocolConfig,
    after: ProtocolConfig,
    changes: list[ProposalChange]
) -> list[str]:
    """Generate recommendations for the proposal."""
    recommendations = []

    # Check if adding costs without revenue
    cost_increases = sum(c.new_value or 0 for c in changes if c.stream_type == "cost" and c.action in ["add", "modify"])
    revenue_increases = sum(c.new_value or 0 for c in changes if c.stream_type == "revenue" and c.action in ["add", "modify"])

    if cost_increases > revenue_increases and cost_increases > 0:
        delta = cost_increases - revenue_increases
        recommendations.append(f"Consider adding ${delta:,.0f}/month in revenue to offset cost increases")

    # Check discretionary costs
    discretionary_costs = sum(
        s.monthly_usd for s in after.cost_streams if s.is_discretionary
    )
    if discretionary_costs > after.monthly_revenue * 0.5:
        recommendations.append(
            f"Discretionary costs (${discretionary_costs:,.0f}/mo) exceed 50% of revenue"
        )

    # Suggest phased rollout for large changes
    if cost_increases > before.monthly_costs * 0.3:
        recommendations.append(
            "Consider phased rollout: start with 50% funding for 3 months, then evaluate"
        )

    return recommendations


def _generate_alternatives(
    protocol: ProtocolConfig,
    changes: list[ProposalChange],
    score_change: int
) -> list[str]:
    """Generate alternative proposals to maintain score."""
    alternatives = []

    if score_change >= 0:
        return []  # No alternatives needed if score improves

    # Find cost increases
    cost_changes = [c for c in changes if c.stream_type == "cost" and c.action in ["add", "modify"]]

    for change in cost_changes:
        if change.action == "add":
            reduced_amount = (change.new_value or 0) * 0.5
            alternatives.append(
                f"Alternative: Add '{change.stream_name}' at ${reduced_amount:,.0f}/mo (50% reduction)"
            )
        elif change.action == "modify":
            # Find original amount
            original = next((s for s in protocol.cost_streams if s.name == change.stream_name), None)
            if original and change.new_value:
                increase = change.new_value - original.monthly_usd
                reduced_increase = increase * 0.5
                alternative_amount = original.monthly_usd + reduced_increase
                alternatives.append(
                    f"Alternative: Increase '{change.stream_name}' to ${alternative_amount:,.0f}/mo (50% of proposed increase)"
                )

    # Suggest offsetting revenue
    total_cost_increase = sum(
        c.new_value or 0 for c in changes
        if c.stream_type == "cost" and c.action == "add"
    )
    if total_cost_increase > 0:
        alternatives.append(
            f"Alternative: Pair with new revenue stream of ${total_cost_increase:,.0f}/mo to maintain runway"
        )

    return alternatives[:3]  # Top 3 alternatives


def parse_proposal_from_cli(args: list[str]) -> list[ProposalChange]:
    """
    Parse proposal changes from CLI arguments.

    Examples:
        --add-cost "New Grant: 2000000"
        --modify-cost "grants: 1500000"
        --add-revenue "New Product: 500000"
        --remove-cost "old_program"

    Args:
        args: List of CLI arguments

    Returns:
        List of ProposalChange objects
    """
    changes = []

    i = 0
    while i < len(args):
        arg = args[i]

        if arg.startswith('--'):
            if i + 1 >= len(args):
                break

            value = args[i + 1]

            if arg == '--add-cost':
                name, amount = _parse_stream_value(value)
                changes.append(ProposalChange(
                    action="add",
                    stream_type="cost",
                    stream_name=name,
                    new_value=amount,
                ))
            elif arg == '--add-revenue':
                name, amount = _parse_stream_value(value)
                changes.append(ProposalChange(
                    action="add",
                    stream_type="revenue",
                    stream_name=name,
                    new_value=amount,
                ))
            elif arg == '--modify-cost':
                name, amount = _parse_stream_value(value)
                changes.append(ProposalChange(
                    action="modify",
                    stream_type="cost",
                    stream_name=name,
                    new_value=amount,
                ))
            elif arg == '--modify-revenue':
                name, amount = _parse_stream_value(value)
                changes.append(ProposalChange(
                    action="modify",
                    stream_type="revenue",
                    stream_name=name,
                    new_value=amount,
                ))
            elif arg == '--remove-cost':
                changes.append(ProposalChange(
                    action="remove",
                    stream_type="cost",
                    stream_name=value,
                ))
            elif arg == '--remove-revenue':
                changes.append(ProposalChange(
                    action="remove",
                    stream_type="revenue",
                    stream_name=value,
                ))

            i += 2
        else:
            i += 1

    return changes


def _parse_stream_value(value: str) -> tuple[str, float]:
    """
    Parse stream name and value from string.

    Examples:
        "New Grant: 2000000" -> ("New Grant", 2000000.0)
        "grants: 1500000" -> ("grants", 1500000.0)
    """
    if ':' in value:
        parts = value.split(':', 1)
        name = parts[0].strip()
        amount = float(parts[1].strip())
        return name, amount
    else:
        raise ValueError(f"Invalid format: {value}. Expected 'name: amount'")
