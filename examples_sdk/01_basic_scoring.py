"""
Example 1: Basic Protocol Scoring

This example shows how to load a protocol config and calculate its Sentinel Score
using the Python SDK.
"""

from sentinel_cloud.protocol_config import ProtocolConfig
from sentinel_cloud.score import calculate_sentinel_score


def main():
    # Load protocol configuration from YAML
    protocol = ProtocolConfig.from_yaml("templates/dao/healthy_dao.yaml")

    print(f"Protocol: {protocol.name}")
    print(f"Type: {protocol.type.value}")
    print(f"Chain: {protocol.chain}")
    print()

    # Display financial overview
    print("Financial Overview:")
    print(f"  Treasury: ${protocol.treasury.balance_usd:,.0f}")
    print(f"  Monthly Revenue: ${protocol.monthly_revenue:,.0f}")
    print(f"  Monthly Costs: ${protocol.monthly_costs:,.0f}")
    print(f"  Monthly Net: ${protocol.monthly_net:,.0f}")
    print()

    # Calculate Sentinel Score
    result = calculate_sentinel_score(protocol)

    # Display results
    print("Sentinel Score:")
    print(f"  Total: {result.total_score}/100")
    print(f"  Grade: {result.grade}")
    print(f"  Status: {result.status}")
    print()

    print("Component Breakdown:")
    print(f"  Runway Score: {result.runway_score}/40")
    print(f"  Sustainability Score: {result.sustainability_score}/30")
    print(f"  Diversification Score: {result.diversification_score}/20")
    print(f"  Trajectory Score: {result.trajectory_score}/10")
    print()

    print("Key Metrics:")
    runway = f"{result.runway_months:.1f} months" if result.runway_months != float('inf') else "∞ (profitable)"
    print(f"  Runway: {runway}")
    ratio = f"{result.sustainability_ratio:.2f}" if result.sustainability_ratio != float('inf') else "∞"
    print(f"  Sustainability Ratio: {ratio}")
    print()

    print("Recommendations:")
    for i, rec in enumerate(result.recommendations, 1):
        print(f"  {i}. {rec}")


if __name__ == "__main__":
    main()
