"""
Phase G: Governance Simulator

Models how parameter changes would play out in governance scenarios.

Answers:
- Will this proposal pass?
- Do whales control governance?
- What's the voting power distribution?
- How long until implementation?
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Literal
from enum import Enum


class VotingMechanism(str, Enum):
    """Voting mechanism type."""
    TOKEN_WEIGHTED = "token_weighted"  # 1 token = 1 vote
    QUADRATIC = "quadratic"  # vote_power = sqrt(tokens)
    ONE_PERSON_ONE_VOTE = "one_person_one_vote"  # 1 user = 1 vote


class ProposalStatus(str, Enum):
    """Proposal lifecycle status."""
    PENDING = "pending"  # Not yet voted
    ACTIVE = "active"  # Currently voting
    PASSED = "passed"  # Approved and will be implemented
    REJECTED = "rejected"  # Did not meet requirements
    QUORUM_NOT_MET = "quorum_not_met"  # Insufficient participation


@dataclass
class GovernanceConfig:
    """
    Governance system configuration.

    Args:
        voting_mechanism: How voting power is calculated
        quorum_pct: Minimum participation required (0-1)
        approval_threshold_pct: Minimum approval required (0-1)
        voting_period_days: How long voting lasts
        implementation_delay_days: Delay after passing before implementation
        allow_abstain: Whether abstain votes count toward quorum
    """
    voting_mechanism: VotingMechanism = VotingMechanism.TOKEN_WEIGHTED
    quorum_pct: float = 0.1  # 10% participation required
    approval_threshold_pct: float = 0.66  # 66% approval required
    voting_period_days: float = 7.0
    implementation_delay_days: float = 2.0
    allow_abstain: bool = True

    def __post_init__(self):
        """Validate configuration."""
        if not 0 <= self.quorum_pct <= 1:
            raise ValueError(f"quorum_pct must be in [0, 1], got {self.quorum_pct}")
        if not 0 <= self.approval_threshold_pct <= 1:
            raise ValueError(f"approval_threshold_pct must be in [0, 1], got {self.approval_threshold_pct}")
        if self.voting_period_days <= 0:
            raise ValueError(f"voting_period_days must be positive, got {self.voting_period_days}")
        if self.implementation_delay_days < 0:
            raise ValueError(f"implementation_delay_days must be non-negative, got {self.implementation_delay_days}")


@dataclass
class Proposal:
    """
    A governance proposal for a parameter change.

    Args:
        title: Proposal title
        param_name: Parameter being changed
        current_value: Current parameter value
        proposed_value: Proposed new value
        description: Optional description
    """
    title: str
    param_name: str
    current_value: float
    proposed_value: float
    description: str = ""

    def change_pct(self) -> float:
        """Calculate percentage change."""
        if self.current_value == 0:
            return float('inf') if self.proposed_value != 0 else 0.0
        return ((self.proposed_value - self.current_value) / self.current_value) * 100


@dataclass
class VoteDistribution:
    """
    How votes are distributed across voters.

    Args:
        votes_for: Dict[voter_id, voting_power] for "yes" votes
        votes_against: Dict[voter_id, voting_power] for "no" votes
        votes_abstain: Dict[voter_id, voting_power] for abstain votes
    """
    votes_for: Dict[int, float] = field(default_factory=dict)
    votes_against: Dict[int, float] = field(default_factory=dict)
    votes_abstain: Dict[int, float] = field(default_factory=dict)

    def total_for(self) -> float:
        """Total voting power in favor."""
        return sum(self.votes_for.values())

    def total_against(self) -> float:
        """Total voting power against."""
        return sum(self.votes_against.values())

    def total_abstain(self) -> float:
        """Total voting power abstaining."""
        return sum(self.votes_abstain.values())

    def total_votes(self) -> float:
        """Total voting power cast."""
        return self.total_for() + self.total_against() + self.total_abstain()

    def total_decided(self) -> float:
        """Total voting power for or against (excluding abstain)."""
        return self.total_for() + self.total_against()


@dataclass
class GovernanceResult:
    """
    Result of a governance simulation.

    Args:
        proposal: The proposal being voted on
        config: Governance configuration used
        vote_distribution: How votes were cast
        total_voting_power: Total possible voting power
        status: Outcome status
        participation_pct: Percentage of voting power that participated
        approval_pct: Percentage of decided votes that approved
        quorum_met: Whether quorum was reached
        threshold_met: Whether approval threshold was met
        days_to_implementation: Days until change is implemented (if passed)
        whale_controlled: Whether top 10 voters control >50% of power
        top_10_share: Voting power share of top 10 voters
    """
    proposal: Proposal
    config: GovernanceConfig
    vote_distribution: VoteDistribution
    total_voting_power: float
    status: ProposalStatus
    participation_pct: float
    approval_pct: float
    quorum_met: bool
    threshold_met: bool
    days_to_implementation: Optional[float] = None
    whale_controlled: bool = False
    top_10_share: float = 0.0

    def summary(self) -> str:
        """Generate human-readable summary."""
        lines = []
        lines.append("=" * 60)
        lines.append("GOVERNANCE SIMULATION RESULT")
        lines.append("=" * 60)
        lines.append(f"Proposal: {self.proposal.title}")
        lines.append(f"Parameter: {self.proposal.param_name}")
        lines.append(f"Change: {self.proposal.current_value:.2f} → {self.proposal.proposed_value:.2f} ({self.proposal.change_pct():+.1f}%)")
        lines.append("")

        # Voting results
        lines.append("VOTING RESULTS")
        lines.append(f"  For:     {self.vote_distribution.total_for():,.0f} ({self.vote_distribution.total_for() / self.total_voting_power * 100:.1f}%)")
        lines.append(f"  Against: {self.vote_distribution.total_against():,.0f} ({self.vote_distribution.total_against() / self.total_voting_power * 100:.1f}%)")
        if self.vote_distribution.total_abstain() > 0:
            lines.append(f"  Abstain: {self.vote_distribution.total_abstain():,.0f} ({self.vote_distribution.total_abstain() / self.total_voting_power * 100:.1f}%)")
        lines.append("")

        # Quorum & threshold
        quorum_icon = "✅" if self.quorum_met else "❌"
        threshold_icon = "✅" if self.threshold_met else "❌"
        lines.append(f"Participation: {self.participation_pct:.1f}% {quorum_icon} (quorum: {self.config.quorum_pct * 100:.1f}%)")
        lines.append(f"Approval:      {self.approval_pct:.1f}% {threshold_icon} (threshold: {self.config.approval_threshold_pct * 100:.1f}%)")
        lines.append("")

        # Status
        status_icons = {
            ProposalStatus.PASSED: "🟢 PASSED",
            ProposalStatus.REJECTED: "🔴 REJECTED",
            ProposalStatus.QUORUM_NOT_MET: "🟡 QUORUM NOT MET",
            ProposalStatus.PENDING: "⚪ PENDING",
            ProposalStatus.ACTIVE: "🔵 ACTIVE",
        }
        lines.append(f"Status: {status_icons.get(self.status, self.status.value.upper())}")

        if self.status == ProposalStatus.PASSED:
            lines.append(f"Implementation: {self.days_to_implementation:.1f} days")
        lines.append("")

        # Governance health
        lines.append("GOVERNANCE HEALTH")
        lines.append(f"  Voting mechanism: {self.config.voting_mechanism.value}")
        lines.append(f"  Top 10 control:   {self.top_10_share:.1f}% {'⚠️  WHALE DOMINATED' if self.whale_controlled else '✅ Decentralized'}")
        lines.append("=" * 60)

        return "\n".join(lines)


def calculate_voting_power(
    token_holdings: Dict[int, float],
    mechanism: VotingMechanism
) -> Dict[int, float]:
    """
    Calculate voting power for each user based on token holdings.

    Args:
        token_holdings: Dict[user_id, token_amount]
        mechanism: Voting mechanism to use

    Returns:
        Dict[user_id, voting_power]
    """
    if mechanism == VotingMechanism.TOKEN_WEIGHTED:
        # 1 token = 1 vote
        return token_holdings.copy()

    elif mechanism == VotingMechanism.QUADRATIC:
        # vote_power = sqrt(tokens)
        return {user: tokens ** 0.5 for user, tokens in token_holdings.items()}

    elif mechanism == VotingMechanism.ONE_PERSON_ONE_VOTE:
        # Everyone gets 1 vote if they hold any tokens
        return {user: 1.0 for user in token_holdings if token_holdings[user] > 0}

    else:
        raise ValueError(f"Unknown voting mechanism: {mechanism}")


def simulate_governance(
    proposal: Proposal,
    token_holdings: Dict[int, float],
    vote_pattern: Dict[int, Literal["for", "against", "abstain"]],
    config: Optional[GovernanceConfig] = None
) -> GovernanceResult:
    """
    Simulate a governance vote on a proposal.

    Args:
        proposal: The proposal being voted on
        token_holdings: Dict[user_id, token_amount] for all users
        vote_pattern: Dict[user_id, vote_choice] for users who vote
        config: Governance configuration (uses defaults if None)

    Returns:
        GovernanceResult with simulation outcome
    """
    if config is None:
        config = GovernanceConfig()

    # Calculate voting power for all token holders
    voting_power = calculate_voting_power(token_holdings, config.voting_mechanism)
    total_voting_power = sum(voting_power.values())

    if total_voting_power == 0:
        raise ValueError("No voting power in system")

    # Distribute votes according to vote_pattern
    vote_distribution = VoteDistribution()

    for user_id, vote_choice in vote_pattern.items():
        if user_id not in voting_power:
            continue  # User has no voting power

        power = voting_power[user_id]

        if vote_choice == "for":
            vote_distribution.votes_for[user_id] = power
        elif vote_choice == "against":
            vote_distribution.votes_against[user_id] = power
        elif vote_choice == "abstain":
            vote_distribution.votes_abstain[user_id] = power
        else:
            raise ValueError(f"Invalid vote choice: {vote_choice}")

    # Calculate metrics
    total_cast = vote_distribution.total_votes()
    participation_pct = (total_cast / total_voting_power) * 100

    # Check quorum (abstain counts if allowed)
    if config.allow_abstain:
        quorum_met = participation_pct >= config.quorum_pct * 100
    else:
        # Only for/against count toward quorum
        decided_pct = (vote_distribution.total_decided() / total_voting_power) * 100
        quorum_met = decided_pct >= config.quorum_pct * 100

    # Calculate approval percentage (of decided votes only)
    decided_total = vote_distribution.total_decided()
    if decided_total > 0:
        approval_pct = (vote_distribution.total_for() / decided_total) * 100
    else:
        approval_pct = 0.0

    # Check approval threshold
    threshold_met = approval_pct >= config.approval_threshold_pct * 100

    # Determine status
    if not quorum_met:
        status = ProposalStatus.QUORUM_NOT_MET
    elif threshold_met:
        status = ProposalStatus.PASSED
    else:
        status = ProposalStatus.REJECTED

    # Calculate implementation timeline
    days_to_implementation = None
    if status == ProposalStatus.PASSED:
        days_to_implementation = config.voting_period_days + config.implementation_delay_days

    # Check for whale control (top 10 voters)
    all_voters = list(voting_power.items())
    all_voters.sort(key=lambda x: x[1], reverse=True)
    top_10_power = sum(power for _, power in all_voters[:10])
    top_10_share = (top_10_power / total_voting_power) * 100
    whale_controlled = top_10_share > 50.0

    return GovernanceResult(
        proposal=proposal,
        config=config,
        vote_distribution=vote_distribution,
        total_voting_power=total_voting_power,
        status=status,
        participation_pct=participation_pct,
        approval_pct=approval_pct,
        quorum_met=quorum_met,
        threshold_met=threshold_met,
        days_to_implementation=days_to_implementation,
        whale_controlled=whale_controlled,
        top_10_share=top_10_share
    )
