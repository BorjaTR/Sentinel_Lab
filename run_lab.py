import os
import subprocess
import argparse

def run_simulation(scenario_file=None):
    """
    Runs the Verilator simulation via Make, injecting the scenario file.
    """
    env = os.environ.copy()
    if scenario_file:
        print(f"🚀 Loading Scenario: {scenario_file}")
        env["SCENARIO_FILE"] = os.path.abspath(scenario_file)
    else:
        print("🎲 Running Random Fuzzer Mode...")

    # Run Make inside the 'tb' directory
    cmd = ["make", "-C", "tb"]
    result = subprocess.run(cmd, env=env, capture_output=True, text=True)
    
    if result.returncode == 0:
        print("\n✅ Simulation Complete!")
        # Extract the TPS from the logs/sim_stats.csv if you want to print it here
        try:
            with open("logs/sim_stats.csv", "r") as f:
                print(f"📊 Report:\n{f.read()}")
        except:
            pass
    else:
        print("\n❌ Simulation Failed!")
        print(result.stderr)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Sentinel Lab Runner")
    parser.add_argument("--scenario", type=str, help="Path to CSV scenario file")
    args = parser.parse_args()
    
    run_simulation(args.scenario)
