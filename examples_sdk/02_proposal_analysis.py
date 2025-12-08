"""
Example 2: Proposal Impact Analysis

This example shows how to simulate governance proposals and analyze their
impact on protocol sustainability.
"""

from sentinel_cloud.protocol_config import ProtocolConfig
from sentinel_cloud.proposal import ProposalChange, analyze_proposal_impact


def main():
    # Load protocol
    protocol = ProtocolConfig.from_yaml("templates/dao/sample.yaml")

    print(f"Analyzing proposal for: {protocol.name}")
    print()

    # Define proposed changes
    changes = [
        ProposalChange(
            action="add",
            stream_type="cost",
            stream_name="New Marketing Campaign",
            new_value=500000,
            description="6-month marketing campaign"
        ),
        ProposalChange(
            action="add",
            stream_type="revenue",
            stream_name="Partnership Revenue",
            new_value=300000,
            description="Expected revenue from new partnership"
        )
    ]

    # Analyze impact
    result = analyze_proposal_impact(protocol, changes)

    # Display results
    print("PROPOSAL CHANGES:")
    for change in changes:
        if change.action == "add":
            print(f"  + Add {change.stream_type}: {change.stream_name} = ${change.new_value:,.0f}/mo")
    print()

    print("SCORE IMPACT:")
    print(f"  Before: {result.before_score.total_score}/100 (Grade {result.before_score.grade})")
    print(f"  After:  {result.after_score.total_score}/100 (Grade {result.after_score.grade})")
    print(f"  Change: {result.score_change:+d} points")
    print()

    print("KEY METRICS:")
    before_runway = f"{result.before_score.runway_months:.1f}mo" if result.before_score.runway_months != float('inf') else "∞"
    after_runway = f"{result.after_score.runway_months:.1f}mo" if result.after_score.runway_months != float('inf') else "∞"
    print(f"  Runway: {before_runway} → {after_runway}")
    print(f"  Sustainability: {result.before_score.sustainability_ratio:.2f} → {result.after_score.sustainability_ratio:.2f}")
    print()

    if result.warnings:
        print("⚠️  WARNINGS:")
        for warning in result.warnings:
            print(f"  {warning}")
        print()

    if result.recommendations:
        print("RECOMMENDATIONS:")
        for i, rec in enumerate(result.recommendations, 1):
            print(f"  {i}. {rec}")
        print()

    if result.alternatives:
        print("ALTERNATIVES:")
        for i, alt in enumerate(result.alternatives, 1):
            print(f"  {i}. {alt}")


if __name__ == "__main__":
    main()
