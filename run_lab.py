import os
import subprocess
import argparse
import csv
import time

def run_simulation(scenario_file=None, fee_bps_asset0=50, fee_bps_asset1=0):
    """
    Runs the Verilator simulation via Make.
    Includes auto-cleaning to ensure fresh binaries.

    Args:
        scenario_file: Path to CSV scenario (optional, uses random fuzzing if None)
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
        
        # Mapping Logic: String Wallets -> Hardware IDs (0-1023)
        mappings = {}
        next_id = 0
        processed_file = "data/processed_batch.csv"
        
        try:
            with open(scenario_file, 'r') as fin, open(processed_file, 'w') as fout:
                reader = csv.DictReader(fin)
                writer = csv.writer(fout)
                writer.writerow(["payer", "payee", "amount0", "amount1", "opcode"])
                
                row_count = 0
                for row in reader:
                    sender = row['sender']
                    receiver = row['receiver']
                    
                    if sender not in mappings:
                        mappings[sender] = next_id
                        next_id = (next_id + 1) % 1024
                    
                    if receiver not in mappings:
                        mappings[receiver] = next_id
                        next_id = (next_id + 1) % 1024
                    
                    # Logic: If compute amount > 0, it's a SWAP (Op 1). Else Transfer (Op 0).
                    amt_usdc = int(row['amount_usdc'])
                    amt_comp = int(row['amount_compute'])
                    opcode = 1 if amt_comp > 0 else 0
                    
                    writer.writerow([mappings[sender], mappings[receiver], amt_usdc, amt_comp, opcode])
                    row_count += 1
            
            print(f"   -> Batch ready: {row_count} transactions.")
            env["SCENARIO_FILE"] = os.path.abspath(processed_file)
            
        except Exception as e:
            print(f"❌ Error processing CSV: {e}")
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
                print(f"📄 Stats Generated:\n{f.read()}")
    else:
        print("\n❌ Simulation Failed!")
        print(result.stderr)
        # Print stdout too, sometimes errors are there
        print(result.stdout)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Sentinel Lab Runner - Hardware Tokenomics Wind Tunnel")
    parser.add_argument("--scenario", type=str, help="Path to CSV scenario file (optional, uses random fuzzing if not provided)")
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

    run_simulation(args.scenario, args.fee_bps_asset0, args.fee_bps_asset1)
