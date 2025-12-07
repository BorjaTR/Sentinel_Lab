"""
Sentinel Cloud - Quick Health Check Example

Demonstrates fast protocol health assessment using the quick_check() SDK method.
Provides 80% of analysis value in <30 seconds.

Usage:
    python examples/02_quick_check.py
"""

from sentinel_cloud import SentinelClient

def main():
    print("="*70)
    print("Sentinel Cloud - Quick Health Check Example")
    print("="*70)
    print()

    client = SentinelClient()

    # Example 1: Healthy protocol (sustainable)
    print("Example 1: Healthy Protocol (fees > emissions)")
    print("-" * 70)
    check = client.quick_check(
        scenario="data/solana_day_1.csv",
        treasury=5_000_000,          # $5M treasury
        current_fee_bps=100,         # 1% fee
        emissions_per_day=10_000,    # $10K/day emissions
        mapper="solana"
    )
    check.print_summary()
    print()

    # Example 2: Warning (low runway)
    print("\nExample 2: Warning - Low Runway")
    print("-" * 70)
    check = client.quick_check(
        scenario="data/solana_day_1.csv",
        treasury=10_000_000,         # $10M treasury
        current_fee_bps=25,          # 0.25% fee
        emissions_per_day=100_000,   # $100K/day emissions
        mapper="solana"
    )
    check.print_summary()
    print()

    # Example 3: Critical (imminent depletion)
    print("\nExample 3: Critical - Imminent Depletion")
    print("-" * 70)
    check = client.quick_check(
        scenario="data/solana_day_1.csv",
        treasury=1_000_000,          # $1M treasury
        current_fee_bps=0,           # No fees
        emissions_per_day=50_000,    # $50K/day emissions
        mapper="solana"
    )
    check.print_summary()
    print()

    # Example 4: Programmatic access
    print("\nExample 4: Programmatic Access")
    print("-" * 70)
    check = client.quick_check(
        scenario="data/solana_day_1.csv",
        treasury=2_000_000,
        current_fee_bps=50,
        emissions_per_day=25_000,
        mapper="solana"
    )

    # Access individual fields
    print(f"Status:      {check.status.value}")
    print(f"Runway:      {check.runway_days:.0f} days" if check.runway_days else "Sustainable")
    print(f"Revenue/day: ${check.revenue_per_day:,.0f}")
    print(f"Burn/day:    ${check.burn_per_day:,.0f}")
    print(f"Net flow:    ${check.net_daily_flow:+,.0f}")
    print()

    # Export to JSON
    import json
    result_dict = check.to_dict()
    print("JSON export sample:")
    print(json.dumps({
        'status': result_dict['status'],
        'runway_days': result_dict['runway_days'],
        'is_sustainable': result_dict['is_sustainable']
    }, indent=2))
    print()

    print("="*70)
    print("Quick Check Examples Complete!")
    print("="*70)
    print("\nKey Takeaways:")
    print("  - quick_check() provides fast health assessment (<30s)")
    print("  - Returns actionable suggestions for sustainability")
    print("  - Perfect for monitoring, alerts, and notebooks")
    print("  - Supports JSON export for integration")
    print()


if __name__ == "__main__":
    main()
