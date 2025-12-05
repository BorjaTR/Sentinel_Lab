import os
import subprocess
import argparse
import csv
import time

def run_simulation(scenario_file=None):
    """
    Runs the Verilator simulation via Make.
    Includes auto-cleaning to ensure fresh binaries.
    """
    # 1. Clean previous stats to avoid stale data reading
    if os.path.exists("logs/sim_stats.csv"):
        os.remove("logs/sim_stats.csv")

    # 2. FORCE CLEAN BUILD (The Fix for "AttributeError")
    # We delete the compiled binary so Verilator must re-read the RTL.
    print("🧹 Cleaning old simulation artifacts...")
    subprocess.run(["rm", "-rf", "tb/sim_build", "tb/results.xml", "tb/__pycache__"], check=False)

    env = os.environ.copy()
    
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
    parser = argparse.ArgumentParser(description="Sentinel Lab Runner")
    parser.add_argument("--scenario", type=str, help="Path to CSV scenario file")
    args = parser.parse_args()
    
    run_simulation(args.scenario)
