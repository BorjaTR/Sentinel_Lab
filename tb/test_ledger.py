import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import sys
import os
import random

class ExchangeModel:
    def __init__(self, num_users=1024):
        self.balances = {i: [1000, 500] for i in range(num_users)}
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

@cocotb.test()
async def test_revenue_stream(dut):
    """
    Day 8: Verify Fee Engine & Business Model
    """
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    model = ExchangeModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("--- 💸 TESTING FEE ENGINE (5,000 TXs) ---")

    # Use larger amounts to ensure fees > 0
    for i in range(5000):
        op = random.randint(0, 1)
        u_a = random.randint(0, 1023)
        u_b = random.randint(0, 1023)
        amt0 = random.randint(2000, 5000) 
        amt1 = random.randint(2000, 5000)

        dut.s_opcode.value = op
        dut.s_user_a.value = u_a
        dut.s_user_b.value = u_b
        dut.s_amount_0.value = amt0
        dut.s_amount_1.value = amt1
        dut.s_valid.value = 1

        model.process(op, u_a, u_b, amt0, amt1)
        await RisingEdge(dut.clk)

    dut.s_valid.value = 0
    for _ in range(10): await RisingEdge(dut.clk)

    # CHECK REVENUE
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
    
    dut._log.info("✅ SUCCESS: Business Model Verified. No leaks.")
