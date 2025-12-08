"""
Sentinel Cloud - Quickstart Example

This example demonstrates the basic workflow for analyzing protocol tokenomics
using Sentinel Cloud's hardware-accelerated simulation engine.

Usage:
    python examples/01_quickstart.py
"""

from sentinel_cloud import SentinelClient

def main():
    print("="*70)
    print("Sentinel Cloud - Quickstart Example")
    print("="*70)
    print()

    # Step 1: Initialize the client
    print("Step 1: Initialize Sentinel Client")
    client = SentinelClient(verbose=True)
    print()

    # Step 2: Run a single simulation
    print("Step 2: Run single simulation with 50 bps (0.50%) fee")
    result = client.run(
        scenario="data/solana_day_1.csv",
        fee_bps=50,
        mapper="solana"
    )

    print(f"\n✓ Simulation complete!")
    print(f"  Revenue:      ${result.revenue_usdc:,.0f}")
    print(f"  Volume:       ${result.volume_usdc:,.0f}")
    print(f"  Transactions: {result.num_tx:,.0f}")
    print(f"  Lab TPS:      {result.lab_tps:,.0f} tx/s")
    print(f"  Wall time:    {result.wall_time:.1f}s")
    print()

    # Step 3: Run a parameter sweep
    print("Step 3: Run parameter sweep (0-100 bps in 25 bps steps)")
    sweep = client.sweep(
        scenario="data/solana_day_1.csv",
        fee_range=(0, 100, 25),  # 0%, 0.25%, 0.50%, 0.75%, 1.00%
        mapper="solana"
    )

    print("\n✓ Sweep complete!")
    sweep.print_summary()
    print()

    # Step 4: Analyze results
    print("Step 4: Find optimal fee configuration")
    optimal = sweep.get_optimal('revenue_usdc')
    print(f"\n✓ Optimal fee: {optimal.fee_bps} bps ({optimal.fee_bps/100:.2f}%)")
    print(f"  Revenue: ${optimal.revenue_usdc:,.0f}")
    print(f"  Volume:  ${optimal.volume_usdc:,.0f}")
    print()

    print("="*70)
    print("Quickstart Complete!")
    print("="*70)
    print("\nNext steps:")
    print("  - Try examples/02_quick_check.py for fast health assessment")
    print("  - Try examples/03_parameter_sweep.py for detailed comparisons")
    print("  - Try examples/04_config_workflow.py for YAML-based workflows")
    print()


if __name__ == "__main__":
    main()
