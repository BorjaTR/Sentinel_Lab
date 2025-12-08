"""Tests for Governance Simulator."""

import pytest
from sentinel_cloud.governance import (
    GovernanceConfig,
    Proposal,
    VoteDistribution,
    VotingMechanism,
    ProposalStatus,
    GovernanceResult,
    calculate_voting_power,
    simulate_governance
)


def test_governance_config_creation():
    """Test GovernanceConfig creation with defaults."""
    config = GovernanceConfig()

    assert config.voting_mechanism == VotingMechanism.TOKEN_WEIGHTED
    assert config.quorum_pct == 0.1
    assert config.approval_threshold_pct == 0.66
    assert config.voting_period_days == 7.0
    assert config.implementation_delay_days == 2.0
    assert config.allow_abstain is True


def test_governance_config_validation_quorum():
    """Test GovernanceConfig validates quorum_pct."""
    with pytest.raises(ValueError, match="quorum_pct must be in"):
        GovernanceConfig(quorum_pct=1.5)

    with pytest.raises(ValueError, match="quorum_pct must be in"):
        GovernanceConfig(quorum_pct=-0.1)


def test_governance_config_validation_threshold():
    """Test GovernanceConfig validates approval_threshold_pct."""
    with pytest.raises(ValueError, match="approval_threshold_pct must be in"):
        GovernanceConfig(approval_threshold_pct=1.5)


def test_governance_config_validation_voting_period():
    """Test GovernanceConfig validates voting_period_days."""
    with pytest.raises(ValueError, match="voting_period_days must be positive"):
        GovernanceConfig(voting_period_days=0)

    with pytest.raises(ValueError, match="voting_period_days must be positive"):
        GovernanceConfig(voting_period_days=-1)


def test_governance_config_validation_implementation_delay():
    """Test GovernanceConfig validates implementation_delay_days."""
    with pytest.raises(ValueError, match="implementation_delay_days must be non-negative"):
        GovernanceConfig(implementation_delay_days=-1)

    # Zero is OK
    config = GovernanceConfig(implementation_delay_days=0)
    assert config.implementation_delay_days == 0


def test_proposal_creation():
    """Test Proposal creation."""
    proposal = Proposal(
        title="Increase transaction fee",
        param_name="fee_bps",
        current_value=10.0,
        proposed_value=15.0,
        description="Raise fees to improve sustainability"
    )

    assert proposal.title == "Increase transaction fee"
    assert proposal.param_name == "fee_bps"
    assert proposal.current_value == 10.0
    assert proposal.proposed_value == 15.0


def test_proposal_change_pct():
    """Test Proposal.change_pct() calculation."""
    # 50% increase
    proposal = Proposal("Test", "param", 10.0, 15.0)
    assert proposal.change_pct() == pytest.approx(50.0)

    # 50% decrease
    proposal = Proposal("Test", "param", 10.0, 5.0)
    assert proposal.change_pct() == pytest.approx(-50.0)

    # No change
    proposal = Proposal("Test", "param", 10.0, 10.0)
    assert proposal.change_pct() == pytest.approx(0.0)


def test_proposal_change_pct_from_zero():
    """Test Proposal.change_pct() when current_value is zero."""
    # From 0 to positive = infinity
    proposal = Proposal("Test", "param", 0.0, 10.0)
    assert proposal.change_pct() == float('inf')

    # From 0 to 0 = 0%
    proposal = Proposal("Test", "param", 0.0, 0.0)
    assert proposal.change_pct() == 0.0


def test_vote_distribution_totals():
    """Test VoteDistribution total calculations."""
    dist = VoteDistribution(
        votes_for={1: 100, 2: 50},
        votes_against={3: 30, 4: 20},
        votes_abstain={5: 10}
    )

    assert dist.total_for() == 150
    assert dist.total_against() == 50
    assert dist.total_abstain() == 10
    assert dist.total_votes() == 210
    assert dist.total_decided() == 200


def test_vote_distribution_empty():
    """Test VoteDistribution with no votes."""
    dist = VoteDistribution()

    assert dist.total_for() == 0
    assert dist.total_against() == 0
    assert dist.total_abstain() == 0
    assert dist.total_votes() == 0
    assert dist.total_decided() == 0


def test_calculate_voting_power_token_weighted():
    """Test token-weighted voting (1 token = 1 vote)."""
    holdings = {1: 100, 2: 50, 3: 25}
    power = calculate_voting_power(holdings, VotingMechanism.TOKEN_WEIGHTED)

    assert power == {1: 100, 2: 50, 3: 25}


def test_calculate_voting_power_quadratic():
    """Test quadratic voting (vote_power = sqrt(tokens))."""
    holdings = {1: 100, 2: 25, 3: 16}
    power = calculate_voting_power(holdings, VotingMechanism.QUADRATIC)

    assert power[1] == pytest.approx(10.0)  # sqrt(100)
    assert power[2] == pytest.approx(5.0)   # sqrt(25)
    assert power[3] == pytest.approx(4.0)   # sqrt(16)


def test_calculate_voting_power_one_person_one_vote():
    """Test one-person-one-vote (everyone gets 1 vote)."""
    holdings = {1: 1000, 2: 10, 3: 1}
    power = calculate_voting_power(holdings, VotingMechanism.ONE_PERSON_ONE_VOTE)

    assert power == {1: 1.0, 2: 1.0, 3: 1.0}


def test_calculate_voting_power_one_person_one_vote_zero_tokens():
    """Test one-person-one-vote filters out zero token holders."""
    holdings = {1: 100, 2: 0, 3: 50}
    power = calculate_voting_power(holdings, VotingMechanism.ONE_PERSON_ONE_VOTE)

    # User 2 with 0 tokens should not get a vote
    assert power == {1: 1.0, 3: 1.0}


def test_simulate_governance_passed():
    """Test governance simulation where proposal passes."""
    proposal = Proposal("Increase fee", "fee_bps", 10.0, 15.0)
    token_holdings = {1: 100, 2: 50, 3: 30, 4: 20}  # Total: 200
    vote_pattern = {
        1: "for",     # 100 votes
        2: "for",     # 50 votes
        3: "against"  # 30 votes
        # User 4 doesn't vote
    }
    config = GovernanceConfig(
        quorum_pct=0.5,  # 50% participation required
        approval_threshold_pct=0.66  # 66% approval required
    )

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    # 180/200 = 90% participation
    assert result.participation_pct == pytest.approx(90.0)

    # 150/180 = 83.3% approval
    assert result.approval_pct == pytest.approx(83.33, abs=0.01)

    # Should pass
    assert result.quorum_met is True
    assert result.threshold_met is True
    assert result.status == ProposalStatus.PASSED
    assert result.days_to_implementation == 9.0  # 7 voting + 2 delay


def test_simulate_governance_rejected():
    """Test governance simulation where proposal is rejected."""
    proposal = Proposal("Decrease fee", "fee_bps", 10.0, 5.0)
    token_holdings = {1: 100, 2: 100}
    vote_pattern = {
        1: "for",     # 100 votes
        2: "against"  # 100 votes
    }
    config = GovernanceConfig(
        quorum_pct=0.5,
        approval_threshold_pct=0.66
    )

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    # 100% participation
    assert result.participation_pct == pytest.approx(100.0)

    # 50% approval (not enough)
    assert result.approval_pct == pytest.approx(50.0)

    # Quorum met but threshold not met
    assert result.quorum_met is True
    assert result.threshold_met is False
    assert result.status == ProposalStatus.REJECTED
    assert result.days_to_implementation is None


def test_simulate_governance_quorum_not_met():
    """Test governance simulation where quorum is not met."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100, 2: 100, 3: 100, 4: 100}  # Total: 400
    vote_pattern = {
        1: "for"  # Only 100/400 = 25% participation
    }
    config = GovernanceConfig(
        quorum_pct=0.5,  # 50% required
        approval_threshold_pct=0.5
    )

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    assert result.participation_pct == pytest.approx(25.0)
    assert result.quorum_met is False
    assert result.status == ProposalStatus.QUORUM_NOT_MET
    assert result.days_to_implementation is None


def test_simulate_governance_with_abstain():
    """Test governance simulation with abstain votes."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100, 2: 50, 3: 50}  # Total: 200
    vote_pattern = {
        1: "for",     # 100
        2: "against", # 50
        3: "abstain"  # 50
    }
    config = GovernanceConfig(
        quorum_pct=0.5,  # 50% required
        approval_threshold_pct=0.5,
        allow_abstain=True  # Abstain counts toward quorum
    )

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    # 200/200 = 100% participation (abstain counts)
    assert result.participation_pct == pytest.approx(100.0)

    # 100/150 = 66.7% approval (abstain doesn't count in approval)
    assert result.approval_pct == pytest.approx(66.67, abs=0.01)

    assert result.quorum_met is True
    assert result.threshold_met is True
    assert result.status == ProposalStatus.PASSED


def test_simulate_governance_abstain_not_allowed():
    """Test governance simulation where abstain doesn't count toward quorum."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100, 2: 50, 3: 50}  # Total: 200
    vote_pattern = {
        1: "for",     # 100
        3: "abstain"  # 50
    }
    config = GovernanceConfig(
        quorum_pct=0.5,  # 50% required
        approval_threshold_pct=0.5,
        allow_abstain=False  # Abstain doesn't count toward quorum
    )

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    # Only 100/200 = 50% decided (abstain doesn't count)
    # This meets the 50% quorum exactly
    assert result.quorum_met is True
    assert result.approval_pct == pytest.approx(100.0)
    assert result.status == ProposalStatus.PASSED


def test_simulate_governance_whale_control():
    """Test governance simulation detects whale control."""
    # Top 10 users control >50% of voting power
    token_holdings = {i: 10 for i in range(1, 11)}  # Top 10: 100 tokens
    for i in range(11, 101):  # Next 90: 90 tokens
        token_holdings[i] = 1

    # Everyone votes for
    vote_pattern = {i: "for" for i in range(1, 101)}

    result = simulate_governance(
        Proposal("Test", "param", 10.0, 15.0),
        token_holdings,
        vote_pattern
    )

    # Top 10 have 100/190 = 52.6%
    assert result.whale_controlled is True
    assert result.top_10_share > 50.0


def test_simulate_governance_not_whale_controlled():
    """Test governance simulation with distributed power."""
    # 100 users with equal tokens
    token_holdings = {i: 10 for i in range(1, 101)}
    vote_pattern = {i: "for" for i in range(1, 101)}

    result = simulate_governance(
        Proposal("Test", "param", 10.0, 15.0),
        token_holdings,
        vote_pattern
    )

    # Top 10 have 100/1000 = 10%
    assert result.whale_controlled is False
    assert result.top_10_share == pytest.approx(10.0)


def test_simulate_governance_quadratic_voting():
    """Test governance simulation with quadratic voting."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100, 2: 25, 3: 16}  # sqrt: 10, 5, 4
    vote_pattern = {
        1: "for",     # 10 votes
        2: "for",     # 5 votes
        3: "against"  # 4 votes
    }
    config = GovernanceConfig(
        voting_mechanism=VotingMechanism.QUADRATIC,
        quorum_pct=0.5,
        approval_threshold_pct=0.5
    )

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    # Total power: 10 + 5 + 4 = 19
    # For: 15, Against: 4
    # Approval: 15/19 = 78.9%
    assert result.approval_pct == pytest.approx(78.95, abs=0.01)
    assert result.status == ProposalStatus.PASSED


def test_simulate_governance_one_person_one_vote():
    """Test governance simulation with one-person-one-vote."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 1000, 2: 10, 3: 1}  # Very unequal holdings
    vote_pattern = {
        1: "for",     # 1 vote
        2: "against", # 1 vote
        3: "against"  # 1 vote
    }
    config = GovernanceConfig(
        voting_mechanism=VotingMechanism.ONE_PERSON_ONE_VOTE,
        quorum_pct=0.5,
        approval_threshold_pct=0.5
    )

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    # 1 for, 2 against = 33.3% approval
    assert result.approval_pct == pytest.approx(33.33, abs=0.01)
    assert result.status == ProposalStatus.REJECTED


def test_simulate_governance_default_config():
    """Test governance simulation with default config."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100, 2: 50}
    vote_pattern = {1: "for", 2: "for"}

    # Should use default config
    result = simulate_governance(proposal, token_holdings, vote_pattern)

    assert result.config.voting_mechanism == VotingMechanism.TOKEN_WEIGHTED
    assert result.config.quorum_pct == 0.1


def test_simulate_governance_no_voting_power():
    """Test governance simulation with no voting power."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {}
    vote_pattern = {}

    with pytest.raises(ValueError, match="No voting power in system"):
        simulate_governance(proposal, token_holdings, vote_pattern)


def test_simulate_governance_invalid_vote_choice():
    """Test governance simulation with invalid vote choice."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100}
    vote_pattern = {1: "maybe"}  # Invalid choice

    with pytest.raises(ValueError, match="Invalid vote choice"):
        simulate_governance(proposal, token_holdings, vote_pattern)


def test_simulate_governance_voter_without_power():
    """Test governance simulation where voter has no tokens."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100}
    vote_pattern = {
        1: "for",
        999: "against"  # User 999 has no tokens
    }

    # Should ignore user 999's vote
    result = simulate_governance(proposal, token_holdings, vote_pattern)

    assert result.vote_distribution.total_for() == 100
    assert result.vote_distribution.total_against() == 0


def test_simulate_governance_zero_decided_votes():
    """Test governance simulation where everyone abstains."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    token_holdings = {1: 100, 2: 50}
    vote_pattern = {1: "abstain", 2: "abstain"}
    config = GovernanceConfig(allow_abstain=True)

    result = simulate_governance(proposal, token_holdings, vote_pattern, config)

    # Quorum met (abstain counts)
    assert result.quorum_met is True

    # But 0% approval (no decided votes)
    assert result.approval_pct == 0.0
    assert result.threshold_met is False
    assert result.status == ProposalStatus.REJECTED


def test_governance_result_summary():
    """Test GovernanceResult.summary() formatting."""
    proposal = Proposal("Increase fee", "fee_bps", 10.0, 15.0)
    config = GovernanceConfig()
    dist = VoteDistribution(
        votes_for={1: 100, 2: 50},
        votes_against={3: 30}
    )

    result = GovernanceResult(
        proposal=proposal,
        config=config,
        vote_distribution=dist,
        total_voting_power=200,
        status=ProposalStatus.PASSED,
        participation_pct=90.0,
        approval_pct=83.3,
        quorum_met=True,
        threshold_met=True,
        days_to_implementation=9.0,
        whale_controlled=False,
        top_10_share=25.0
    )

    summary = result.summary()

    # Check key elements
    assert "GOVERNANCE SIMULATION RESULT" in summary
    assert "Increase fee" in summary
    assert "fee_bps" in summary
    assert "10.00 → 15.00" in summary
    assert "+50.0%" in summary  # Change percentage
    assert "For:" in summary
    assert "Against:" in summary
    assert "Participation: 90.0%" in summary
    assert "Approval:      83.3%" in summary
    assert "🟢 PASSED" in summary
    assert "Implementation: 9.0 days" in summary
    assert "Top 10 control:   25.0%" in summary
    assert "✅ Decentralized" in summary


def test_governance_result_summary_whale_controlled():
    """Test summary shows whale control warning."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    config = GovernanceConfig()
    dist = VoteDistribution(votes_for={1: 100})

    result = GovernanceResult(
        proposal=proposal,
        config=config,
        vote_distribution=dist,
        total_voting_power=100,
        status=ProposalStatus.PASSED,
        participation_pct=100.0,
        approval_pct=100.0,
        quorum_met=True,
        threshold_met=True,
        days_to_implementation=9.0,
        whale_controlled=True,
        top_10_share=75.0
    )

    summary = result.summary()

    assert "⚠️  WHALE DOMINATED" in summary


def test_governance_result_summary_rejected():
    """Test summary for rejected proposal."""
    proposal = Proposal("Test", "param", 10.0, 15.0)
    config = GovernanceConfig()
    dist = VoteDistribution(votes_for={1: 30}, votes_against={2: 70})

    result = GovernanceResult(
        proposal=proposal,
        config=config,
        vote_distribution=dist,
        total_voting_power=100,
        status=ProposalStatus.REJECTED,
        participation_pct=100.0,
        approval_pct=30.0,
        quorum_met=True,
        threshold_met=False,
        whale_controlled=False,
        top_10_share=10.0
    )

    summary = result.summary()

    assert "🔴 REJECTED" in summary
    assert "Implementation:" not in summary  # No implementation for rejected


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
