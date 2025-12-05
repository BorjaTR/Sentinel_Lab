"""
Debug test to isolate the fee/forwarding issue
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

class ExchangeModel:
    def __init__(self, num_users=1024):
        self.balances = {i: [1000000, 1000000] for i in range(num_users)}
        self.vault = [0, 0]
    
    def process(self, op, u_a, u_b, amt0, amt1):
        if u_a == u_b: return True
        
        bal_a = self.balances[u_a]
        bal_b = self.balances[u_b]
        
        fee0 = amt0 >> 11
        fee1 = amt1 >> 11
        
        if op == 0:
            if bal_a[0] >= (amt0 + fee0):
                bal_a[0] -= (amt0 + fee0)
                bal_b[0] += amt0
                self.vault[0] += fee0
                return True
        elif op == 1:
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
async def test_fee_accumulation(dut):
    """Check if fee calculation matches between HW and model"""
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()
    
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)
    
    dut._log.info("=== Debugging Fee Calculation ===")
    
    # Simple sequence: 10 transfers
    for i in range(10):
        dut.s_opcode.value = 0  # Transfer
        dut.s_user_a.value = i
        dut.s_user_b.value = i + 1
        dut.s_amount_0.value = 10000
        dut.s_amount_1.value = 0
        dut.s_valid.value = 1
        
        model.process(0, i, i+1, 10000, 0)
        await RisingEdge(dut.clk)
    
    dut.s_valid.value = 0
    for _ in range(5): await RisingEdge(dut.clk)
    
    # Check vault
    hw_vault = int(dut.m_vault_usdc.value)
    model_vault = model.vault[0]
    
    dut._log.info(f"HW Vault: {hw_vault}, Model Vault: {model_vault}")
    assert hw_vault == model_vault, f"Vault mismatch! HW:{hw_vault} Model:{model_vault}"
    
    # Check individual balances
    for i in range(12):
        raw = int(dut.portfolios[i].value)
        hw_usdc = raw & 0xFFFFFFFFFFFFFFFF
        model_usdc = model.balances[i][0]
        if hw_usdc != model_usdc:
            dut._log.error(f"User {i}: HW:{hw_usdc} Model:{model_usdc} Diff:{hw_usdc-model_usdc}")
    
    dut._log.info("Test complete")
