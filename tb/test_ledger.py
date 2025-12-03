import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import sys
import os
import csv
import random

sys.path.append(os.path.join(os.path.dirname(__file__), "../model"))
from ledger_model import LedgerModel

# Helper to read CSV
def load_scenario(filename):
    trades = []
    with open(filename, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            trades.append((int(row['payer']), int(row['payee']), int(row['amount'])))
    return trades

@cocotb.test()
async def run_ledger(dut):
    """
    Main Execution Engine.
    Mode A: Random Fuzzing (Default)
    Mode B: CSV Replay (If SCENARIO_FILE env var is set)
    """
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    model = LedgerModel()

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    # Check for Scenario File
    scenario_path = os.environ.get("SCENARIO_FILE")
    
    if scenario_path:
        dut._log.info(f"--- 📂 LOADING SCENARIO: {scenario_path} ---")
        trades = load_scenario(scenario_path)
    else:
        dut._log.info("--- 🎲 MODE: RANDOM FUZZING (5000 TXs) ---")
        trades = []
        for _ in range(5000):
            trades.append((random.randint(0,1023), random.randint(0,1023), random.randint(1,100)))

    # EXECUTION LOOP
    start_time = cocotb.utils.get_sim_time(units='ns')
    
    for i, (payer, payee, amount) in enumerate(trades):
        dut.s_payer.value = payer
        dut.s_payee.value = payee
        dut.s_amount.value = amount
        dut.s_valid.value = 1
        
        model.process_transaction(payer, payee, amount)
        await RisingEdge(dut.clk)
        
        # Periodic Progress Log
        if i % 1000 == 0:
            dut._log.info(f"Processed {i} transactions...")

    # COOLDOWN
    dut.s_valid.value = 0
    for _ in range(20): await RisingEdge(dut.clk)
    
    end_time = cocotb.utils.get_sim_time(units='ns')
    duration = end_time - start_time
    tps = len(trades) / (duration / 1e9) / 1e6 # Million TPS

    # VERIFICATION
    errors = 0
    for i in range(1024):
        hw_bal = int(dut.balances[i].value)
        exp_bal = model.balances[i]
        if hw_bal != exp_bal:
            dut._log.error(f"❌ User {i}: HW {hw_bal} != Model {exp_bal}")
            errors += 1
            
    if errors == 0:
        dut._log.info(f"✅ SUCCESS. Throughput: {tps:.2f} Million TPS")
        # Write stats for the dashboard to read later
        with open("../logs/sim_stats.csv", "w") as f:
            f.write(f"metric,value\n")
            f.write(f"total_tx,{len(trades)}\n")
            f.write(f"duration_ns,{duration}\n")
            f.write(f"tps_million,{tps:.2f}\n")
            f.write(f"latency_cycles,1\n")
    else:
        assert False, f"Ledger corrupted! {errors} mismatches."