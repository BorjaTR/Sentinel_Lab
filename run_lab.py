import os
import subprocess
import argparse
import csv
import time

# Import Sentinel Cloud normalization pipeline
from sentinel_cloud import load_and_normalize, convert_to_testbench_format

def run_simulation(scenario_file=None, mapper='solana', fee_bps_asset0=50, fee_bps_asset1=0):
    """
    Runs the Verilator simulation via Make.
    Includes auto-cleaning to ensure fresh binaries.

    Args:
        scenario_file: Path to CSV scenario (optional, uses random fuzzing if None)
        mapper: Protocol mapper ('solana', 'evm', 'depin', etc.) for normalizing external CSVs
        fee_bps_asset0: Fee in basis points for asset 0 (USDC), 0-10000 (default: 50 = 0.50%)
        fee_bps_asset1: Fee in basis points for asset 1 (GPU credits), 0-10000 (default: 0 = 0%)
    """
    # 1. Clean previous stats to avoid stale data reading
    if os.path.exists("logs/sim_stats.csv"):
        os.remove("logs/sim_stats.csv")

    # 2. FORCE CLEAN BUILD (The Fix for "AttributeError")
    # We delete the compiled binary so Verilator must re-read the RTL.
    print("🧹 Cleaning old simulation artifacts...")
    subprocess.run(["rm", "-rf", "tb/sim_build", "tb/results.xml", "tb/__pycache__"], check=False)

    env = os.environ.copy()

    # Configure fees via environment variables (passed to cocotb test)
    env["FEE_BPS_ASSET0"] = str(fee_bps_asset0)
    env["FEE_BPS_ASSET1"] = str(fee_bps_asset1)
    print(f"⚙️  Fee Config: Asset0={fee_bps_asset0} bps ({fee_bps_asset0/100:.2f}%), Asset1={fee_bps_asset1} bps ({fee_bps_asset1/100:.2f}%)")
    
    if scenario_file:
        print(f"🚀 Ingesting Mainnet Data: {scenario_file}")
        print(f"   Protocol: {mapper}")

        processed_file = "data/processed_batch.csv"

        try:
            # Load and normalize using Sentinel Cloud pipeline
            # External CSV → Protocol Mapper → Canonical SentinelTx → Testbench Format
            transactions = load_and_normalize(
                csv_path=scenario_file,
                mapper=mapper,
                num_users=1024,
                validate=True
            )

            # Convert canonical format to testbench CSV
            convert_to_testbench_format(transactions, processed_file)

            print(f"   -> Batch ready: {len(transactions)} transactions normalized.")
            env["SCENARIO_FILE"] = os.path.abspath(processed_file)

        except FileNotFoundError as e:
            print(f"❌ Error: CSV file not found: {e}")
            return
        except ValueError as e:
            print(f"❌ Error normalizing transactions: {e}")
            return
        except Exception as e:
            print(f"❌ Unexpected error processing CSV: {e}")
            return

    # 3. Run Hardware Simulation
    print("⚙️  Compiling & Running Verilator...")
    start_time = time.time()
    cmd = ["make", "-C", "tb"]
    result = subprocess.run(cmd, env=env, capture_output=True, text=True)
    end_time = time.time()
    
    if result.returncode == 0:
        print("\n✅ Simulation Complete!")
        print(f"   -> Wall Clock Time: {end_time - start_time:.4f}s")

        # Optional: Print the report to terminal
        if os.path.exists("logs/sim_stats.csv"):
            with open("logs/sim_stats.csv", "r") as f:
                stats = {}
                for line in f:
                    if ',' in line and line.strip() != "metric,value":
                        k, v = line.strip().split(',', 1)
                        stats[k] = v

                if 'tps_million' in stats:
                    print(f"\n📊 Performance Metrics:")
                    print(f"   Engine TPS: {stats['tps_million']}M tx/s (RTL simulation @ 100MHz, 1 tx/cycle)")
                    print(f"   Note: Excludes I/O, networking, and consensus overhead")
                    if 'rev_usdc' in stats:
                        print(f"   Revenue: ${int(stats['rev_usdc']):,} USDC")
                    if 'vol_usdc' in stats:
                        print(f"   Volume: ${int(stats['vol_usdc']):,} USDC")
    else:
        print("\n❌ Simulation Failed!")
        print(result.stderr)
        # Print stdout too, sometimes errors are there
        print(result.stdout)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Sentinel Lab Runner - Hardware Tokenomics Wind Tunnel")
    parser.add_argument("--scenario", type=str, help="Path to CSV scenario file (optional, uses random fuzzing if not provided)")
    parser.add_argument("--mapper", type=str, default="solana",
                        choices=['solana', 'evm', 'ethereum', 'arbitrum', 'polygon', 'depin', 'depin_rewards', 'depin_penalty', 'helium', 'filecoin', 'render'],
                        help="Protocol mapper for normalizing external CSV (default: solana)")
    parser.add_argument("--fee-bps-asset0", type=int, default=50,
                        help="Fee for asset 0 (USDC) in basis points (0-10000). Default: 50 = 0.50%%")
    parser.add_argument("--fee-bps-asset1", type=int, default=0,
                        help="Fee for asset 1 (GPU credits) in basis points (0-10000). Default: 0 = 0%%")
    args = parser.parse_args()

    # Validate fee ranges
    if not (0 <= args.fee_bps_asset0 <= 10000):
        print("❌ Error: --fee-bps-asset0 must be between 0 and 10000")
        exit(1)
    if not (0 <= args.fee_bps_asset1 <= 10000):
        print("❌ Error: --fee-bps-asset1 must be between 0 and 10000")
        exit(1)

    run_simulation(args.scenario, args.mapper, args.fee_bps_asset0, args.fee_bps_asset1)
