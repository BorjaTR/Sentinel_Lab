"""
Sentinel Cloud - Parameter Sweep Example

Demonstrates how to run comprehensive fee sweeps to find optimal configurations.

Usage:
    python examples/03_parameter_sweep.py
"""

from sentinel_cloud import SentinelClient
from sentinel_cloud.dashboard_io import save_experiment

def main():
    print("="*70)
    print("Sentinel Cloud - Parameter Sweep Example")
    print("="*70)
    print()

    client = SentinelClient(verbose=True)

    # Example 1: Basic fee sweep
    print("Example 1: Basic Fee Sweep (0-2% in 0.25% steps)")
    print("-" * 70)
    sweep = client.sweep(
        scenario="data/solana_day_1.csv",
        fee_range=(0, 200, 25),  # 0 bps to 200 bps in 25 bps steps
        mapper="solana"
    )

    sweep.print_summary()
    print()

    # Find optimal by different metrics
    print("\nOptimal Configurations:")
    print("-" * 70)

    optimal_revenue = sweep.get_optimal('revenue_usdc')
    print(f"By Revenue:    {optimal_revenue.fee_bps} bps → ${optimal_revenue.revenue_usdc:,.0f}")

    optimal_volume = sweep.get_optimal('volume_usdc')
    print(f"By Volume:     {optimal_volume.fee_bps} bps → ${optimal_volume.volume_usdc:,.0f}")

    optimal_tps = sweep.get_optimal('lab_tps')
    print(f"By Throughput: {optimal_tps.fee_bps} bps → {optimal_tps.lab_tps:,.0f} TPS")
    print()

    # Get detailed analysis
    print("\nDetailed Fee Sweep Analysis:")
    print("-" * 70)
    sweep.print_analysis()
    print()

    # Example 2: Explicit fee list
    print("\nExample 2: Explicit Fee List")
    print("-" * 70)
    sweep = client.sweep(
        scenario="data/solana_day_1.csv",
        fee_list=[0, 50, 100, 150, 250, 500],  # Test specific fees
        mapper="solana"
    )

    sweep.print_summary()
    print()

    # Example 3: Save results for dashboard
    print("\nExample 3: Save Results for Dashboard")
    print("-" * 70)
    sweep = client.sweep(
        scenario="data/solana_day_1.csv",
        fee_range=(0, 100, 25),
        mapper="solana"
    )

    # Save to experiments directory
    saved_path = save_experiment(sweep._experiment_result, "experiments")
    print(f"✓ Results saved to: {saved_path}")
    print(f"  Open dashboard with: streamlit run dashboard_v3.py")
    print()

    # Example 4: Programmatic analysis
    print("\nExample 4: Programmatic Analysis")
    print("-" * 70)

    successful = sweep.get_successful()
    print(f"Successful runs: {len(successful)}")

    for result in successful:
        efficiency = result.revenue_usdc / result.volume_usdc if result.volume_usdc > 0 else 0
        print(f"  {result.fee_bps:3d} bps: Revenue ${result.revenue_usdc:>12,.0f} "
              f"(efficiency: {efficiency*10000:.2f} bps)")
    print()

    print("="*70)
    print("Parameter Sweep Examples Complete!")
    print("="*70)
    print("\nKey Takeaways:")
    print("  - Use fee_range for uniform sweeps")
    print("  - Use fee_list for specific configurations")
    print("  - get_optimal() finds best configuration by metric")
    print("  - Results can be saved for dashboard visualization")
    print()


if __name__ == "__main__":
    main()
