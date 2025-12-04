#!/usr/bin/env python3
"""
Sentinel Lab Experiment Runner

Run parameter sweeps and A/B tests across multiple configurations.

Examples:
    # Fee sweep from 0% to 2.0% in 0.5% increments
    python3 run_experiment.py --scenario data/solana_day_1.csv --mapper solana \\
        --sweep-fee-start 0 --sweep-fee-end 200 --sweep-fee-step 50

    # Compare specific fee points
    python3 run_experiment.py --scenario data/solana_day_1.csv --mapper solana \\
        --fees 0 25 50 100 200

    # Export results to JSON
    python3 run_experiment.py --scenario data/solana_day_1.csv --mapper solana \\
        --fees 0 50 100 --export results.json
"""

import argparse
import sys
from sentinel_cloud import (
    Config,
    run_experiments,
    generate_fee_sweep_configs
)


def main():
    parser = argparse.ArgumentParser(
        description="Sentinel Lab Experiment Runner - Parameter Sweep & A/B Testing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Fee sweep from 0% to 2.0% in 0.25% increments
  python3 run_experiment.py --scenario data/solana_day_1.csv --sweep-fee-start 0 --sweep-fee-end 200 --sweep-fee-step 25

  # Test specific fee points
  python3 run_experiment.py --scenario data/solana_day_1.csv --fees 0 50 100 200

  # Quick 3-point comparison
  python3 run_experiment.py --scenario data/solana_day_1.csv --fees 0 50 100
        """
    )

    parser.add_argument(
        "--scenario",
        type=str,
        required=True,
        help="Path to transaction CSV file"
    )

    parser.add_argument(
        "--mapper",
        type=str,
        default="solana",
        choices=['solana', 'evm', 'ethereum', 'arbitrum', 'polygon', 'depin', 'helium', 'filecoin', 'render'],
        help="Protocol mapper for normalizing CSV (default: solana)"
    )

    # Fee sweep mode
    parser.add_argument(
        "--sweep-fee-start",
        type=int,
        help="Starting fee in basis points for sweep (e.g., 0)"
    )

    parser.add_argument(
        "--sweep-fee-end",
        type=int,
        help="Ending fee in basis points for sweep (e.g., 200)"
    )

    parser.add_argument(
        "--sweep-fee-step",
        type=int,
        default=25,
        help="Step size in basis points for sweep (default: 25 = 0.25%%)"
    )

    # Explicit fee list mode
    parser.add_argument(
        "--fees",
        type=int,
        nargs='+',
        help="Explicit list of fees to test in basis points (e.g., 0 25 50 100)"
    )

    # Output options
    parser.add_argument(
        "--export",
        type=str,
        help="Export results to JSON file"
    )

    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress progress output"
    )

    args = parser.parse_args()

    # Generate configs
    configs = []

    if args.fees:
        # Explicit fee list
        for fee_bps in args.fees:
            if not (0 <= fee_bps <= 10000):
                print(f"❌ Error: Fee {fee_bps} bps is out of range [0, 10000]")
                sys.exit(1)
            name = f"{fee_bps} bps ({fee_bps/100:.2f}%)"
            configs.append(Config(name=name, fee_bps_asset0=fee_bps))

    elif args.sweep_fee_start is not None and args.sweep_fee_end is not None:
        # Fee sweep
        if not (0 <= args.sweep_fee_start <= 10000):
            print(f"❌ Error: sweep-fee-start must be in [0, 10000]")
            sys.exit(1)
        if not (0 <= args.sweep_fee_end <= 10000):
            print(f"❌ Error: sweep-fee-end must be in [0, 10000]")
            sys.exit(1)
        if args.sweep_fee_start > args.sweep_fee_end:
            print(f"❌ Error: sweep-fee-start must be <= sweep-fee-end")
            sys.exit(1)

        configs = generate_fee_sweep_configs(
            start_bps=args.sweep_fee_start,
            end_bps=args.sweep_fee_end,
            step_bps=args.sweep_fee_step,
            asset=0
        )

    else:
        # Default: quick 4-point test
        print("ℹ️  No fees specified, using default: 0, 25, 50, 100 bps")
        configs = [
            Config("No Fee (0.00%)", fee_bps_asset0=0),
            Config("Low (0.25%)", fee_bps_asset0=25),
            Config("Standard (0.50%)", fee_bps_asset0=50),
            Config("High (1.00%)", fee_bps_asset0=100),
        ]

    if len(configs) == 0:
        print("❌ Error: No configurations generated")
        sys.exit(1)

    # Run experiments
    try:
        result = run_experiments(
            scenario_path=args.scenario,
            mapper=args.mapper,
            configs=configs,
            verbose=not args.quiet
        )

        # Phase 3.5: Add interpretation layer
        # Only show analysis if we have multiple configs (sweep scenario)
        if len(result.get_successful_runs()) >= 2 and not args.quiet:
            result.summarize_fee_sweep()

        # Export if requested
        if args.export:
            result.to_json(args.export)
            print(f"💾 Results exported to: {args.export}")

        # Exit with success/failure code
        failed_runs = [r for r in result.runs if not r.success]
        if failed_runs:
            print(f"\n⚠️  {len(failed_runs)} configuration(s) failed")
            sys.exit(1)
        else:
            print(f"\n✅ All {len(result.runs)} configurations completed successfully")
            sys.exit(0)

    except FileNotFoundError as e:
        print(f"❌ Error: Scenario file not found: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
