import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import sys
import os
import random
import csv

class ExchangeModel:
    def __init__(self, num_users=1024):
        self.balances = {i: [1000, 500] for i in range(num_users)}
        self.vault = [0, 0] # [USDC, GPU]
        self.vol_usdc = 0
        self.vol_gpu = 0

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
                self.vol_usdc += amt0
                return True
        elif op == 1: # Swap
            if bal_a[0] >= (amt0 + fee0) and bal_b[1] >= (amt1 + fee1):
                bal_a[0] -= (amt0 + fee0)
                bal_a[1] += amt1
                bal_b[0] += amt0
                bal_b[1] -= (amt1 + fee1)
                self.vault[0] += fee0
                self.vault[1] += fee1
                self.vol_usdc += amt0
                self.vol_gpu += amt1
                return True
        return False

@cocotb.test()
async def test_revenue_stream(dut):
    """
    Cocotb Test: Verify Hardware Against Golden Model
    """
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    # Check if CSV scenario is provided
    scenario_file = os.environ.get("SCENARIO_FILE", None)
    transactions = []

    if scenario_file and os.path.exists(scenario_file):
        dut._log.info(f"🚀 LOADING CSV SCENARIO: {scenario_file}")
        with open(scenario_file, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                transactions.append({
                    'op': int(row['opcode']),
                    'u_a': int(row['payer']),
                    'u_b': int(row['payee']),
                    'amt0': int(row['amount0']),
                    'amt1': int(row['amount1'])
                })
        dut._log.info(f"   -> Loaded {len(transactions)} transactions from CSV")
    else:
        # Random fuzzing mode
        dut._log.info("🎲 RANDOM FUZZING MODE (5,000 TXs)")
        for _ in range(5000):
            transactions.append({
                'op': random.randint(0, 1),
                'u_a': random.randint(0, 1023),
                'u_b': random.randint(0, 1023),
                'amt0': random.randint(2000, 5000),
                'amt1': random.randint(2000, 5000)
            })

    # Execute all transactions
    start_time = cocotb.utils.get_sim_time('ns')

    for tx in transactions:
        dut.s_opcode.value = tx['op']
        dut.s_user_a.value = tx['u_a']
        dut.s_user_b.value = tx['u_b']
        dut.s_amount_0.value = tx['amt0']
        dut.s_amount_1.value = tx['amt1']
        dut.s_valid.value = 1

        model.process(tx['op'], tx['u_a'], tx['u_b'], tx['amt0'], tx['amt1'])
        await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    end_time = cocotb.utils.get_sim_time('ns')
    duration_ns = end_time - start_time
    tps = (len(transactions) / duration_ns) * 1_000

    # CHECK REVENUE VERIFICATION
    hw_vault_usdc = int(dut.m_vault_usdc.value)
    hw_vault_gpu  = int(dut.m_vault_gpu.value)

    dut._log.info(f"💰 Total Revenue: {hw_vault_usdc} USDC, {hw_vault_gpu} GPU Credits")

    assert hw_vault_usdc == model.vault[0], f"Vault USDC Mismatch! HW:{hw_vault_usdc} Mod:{model.vault[0]}"
    assert hw_vault_gpu == model.vault[1], f"Vault GPU Mismatch! HW:{hw_vault_gpu} Mod:{model.vault[1]}"

    # CHECK CONSERVATION (Users + Vault)
    total_usdc_hw = hw_vault_usdc
    total_gpu_hw = hw_vault_gpu

    for i in range(1024):
        raw = int(dut.portfolios[i].value)
        total_usdc_hw += raw & 0xFFFFFFFFFFFFFFFF
        total_gpu_hw += (raw >> 64) & 0xFFFFFFFFFFFFFFFF

    initial_usdc = 1024 * 1000
    initial_gpu = 1024 * 500

    assert total_usdc_hw == initial_usdc, "Leak Detected in USDC!"
    assert total_gpu_hw == initial_gpu, "Leak Detected in GPU!"

    dut._log.info(f"✅ SUCCESS: Processed {len(transactions)} TXs | {tps:.2f} Million TPS | No leaks detected.")

    # Write statistics to CSV
    os.makedirs("../logs", exist_ok=True)
    with open("../logs/sim_stats.csv", 'w') as f:
        f.write("metric,value\n")
        f.write(f"total_tx,{len(transactions)}\n")
        f.write(f"duration_ns,{duration_ns}\n")
        f.write(f"tps_million,{tps:.2f}\n")
        f.write(f"latency_cycles,1\n")
        f.write(f"rev_usdc,{hw_vault_usdc}\n")
        f.write(f"rev_gpu,{hw_vault_gpu}\n")
        f.write(f"vol_usdc,{model.vol_usdc}\n")
        f.write(f"vol_gpu,{model.vol_gpu}\n")
