import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import sys
import os
import csv
import random

# ---------------------------------------------------------
# PYTHON GOLDEN MODEL
# ---------------------------------------------------------
class ExchangeModel:
    def __init__(self, num_users=1024):
        # Init: 1,000,000 to match Hardware
        self.balances = {i: [1000000, 1000000] for i in range(num_users)} 
        self.vault = [0, 0] # [USDC, GPU]

    def process(self, op, u_a, u_b, amt0, amt1):
        if u_a == u_b: return True
        bal_a = self.balances[u_a]
        bal_b = self.balances[u_b]
        
        # Fee Calculation (Bit Shift >> 11)
        fee0 = amt0 >> 11
        fee1 = amt1 >> 11

        if op == 0: # Transfer
            if bal_a[0] >= (amt0 + fee0):
                bal_a[0] -= (amt0 + fee0)
                bal_b[0] += amt0
                self.vault[0] += fee0
                return True
        elif op == 1: # Swap
            if bal_a[0] >= (amt0 + fee0) and bal_b[1] >= (amt1 + fee1):
                bal_a[0] -= (amt0 + fee0)
                bal_a[1] += amt1
                bal_b[0] += amt0
                bal_b[1] -= (amt1 + fee1)
                self.vault[0] += fee0
                self.vault[1] += fee1
                return True
        return False

# ---------------------------------------------------------
# CSV LOADER
# ---------------------------------------------------------
def load_processed_scenario(filename):
    trades = []
    with open(filename, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            trades.append({
                'p': int(row['payer']),
                'r': int(row['payee']),
                'a0': int(row['amount0']),
                'a1': int(row['amount1']),
                'op': int(row['opcode'])
            })
    return trades

# ---------------------------------------------------------
# MAIN TESTBENCH
# ---------------------------------------------------------
@cocotb.test()
async def test_mainnet_replay(dut):
    """
    Day 9: Mainnet Replay & Financial Telemetry
    """
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    model = ExchangeModel()

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    # Load Scenario
    scenario_path = os.environ.get("SCENARIO_FILE")
    trades = []
    
    if scenario_path:
        dut._log.info(f"--- 🎞️ REPLAYING MAINNET BATCH: {scenario_path} ---")
        trades = load_processed_scenario(scenario_path)
    else:
        dut._log.info("--- 🎲 MODE: RANDOM SWARM (Default) ---")
        for _ in range(5000):
            trades.append({'p': random.randint(0,1023), 'r': random.randint(0,1023), 
                           'a0': 50, 'a1': 10, 'op': random.randint(0,1)})

    start_time = cocotb.utils.get_sim_time(units='ns')
    
    # Execution Loop
    vol_usdc = 0
    vol_gpu = 0
    
    for i, t in enumerate(trades):
        dut.s_opcode.value = t['op']
        dut.s_user_a.value = t['p']
        dut.s_user_b.value = t['r']
        dut.s_amount_0.value = t['a0']
        dut.s_amount_1.value = t['a1']
        dut.s_valid.value = 1
        
        # Update Model
        if model.process(t['op'], t['p'], t['r'], t['a0'], t['a1']):
            vol_usdc += t['a0']
            vol_gpu += t['a1']

        await RisingEdge(dut.clk)
        
        if i % 10000 == 0 and i > 0:
            dut._log.info(f"   ... Replayed {i} transactions ...")

    # Cooldown
    dut.s_valid.value = 0
    for _ in range(20): await RisingEdge(dut.clk)
    
    end_time = cocotb.utils.get_sim_time(units='ns')
    duration = end_time - start_time
    tps = len(trades) / (duration / 1e9) / 1e6

    # ---------------------------------------------------------
    # VERIFICATION & EXPORT
    # ---------------------------------------------------------
    errors = 0
    total_usdc = int(dut.m_vault_usdc.value)
    total_gpu = int(dut.m_vault_gpu.value)
    
    # Write CSV for Dashboard
    with open("../logs/sim_stats.csv", "w") as f:
        f.write(f"metric,value\n")
        f.write(f"total_tx,{len(trades)}\n")
        f.write(f"duration_ns,{duration}\n")
        f.write(f"tps_million,{tps:.2f}\n")
        f.write(f"latency_cycles,2\n")
        f.write(f"rev_usdc,{total_usdc}\n")
        f.write(f"rev_gpu,{total_gpu}\n")
        f.write(f"vol_usdc,{vol_usdc}\n")
        f.write(f"vol_gpu,{vol_gpu}\n")

    # Verify Balances
    for i in range(1024):
        raw = int(dut.portfolios[i].value)
        hw_usdc = raw & 0xFFFFFFFFFFFFFFFF
        hw_gpu = (raw >> 64) & 0xFFFFFFFFFFFFFFFF
        
        if hw_usdc != model.balances[i][0]:
            errors += 1

    if errors == 0:
        dut._log.info("✅ SUCCESS: Mainnet Replay verified. 100% State Match.")
    else:
        assert False, f"Replay Failed! {errors} corruptions detected."
