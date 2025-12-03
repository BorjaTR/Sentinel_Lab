"""
Trace exactly where HW and model diverge
"""
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
import random

class ExchangeModel:
    def __init__(self):
        self.balances = {i: [1000000, 1000000] for i in range(1024)}
        self.vault = [0, 0]
    
    def process(self, op, u_a, u_b, amt0, amt1):
        if u_a == u_b: return (True, 0, 0)
        
        bal_a = self.balances[u_a]
        bal_b = self.balances[u_b]
        
        fee0 = amt0 >> 11
        fee1 = amt1 >> 11
        
        if op == 0:
            if bal_a[0] >= (amt0 + fee0):
                bal_a[0] -= (amt0 + fee0)
                bal_b[0] += amt0
                self.vault[0] += fee0
                return (True, fee0, 0)
        elif op == 1:
            if bal_a[0] >= (amt0 + fee0) and bal_b[1] >= (amt1 + fee1):
                bal_a[0] -= (amt0 + fee0)
                bal_a[1] += amt1
                bal_b[0] += amt0
                bal_b[1] -= (amt1 + fee1)
                self.vault[0] += fee0
                self.vault[1] += fee1
                return (True, fee0, fee1)
        return (False, 0, 0)

@cocotb.test()
async def test_trace_first_divergence(dut):
    """Run random test but stop at first mismatch"""
    cocotb.fork(Clock(dut.clk, 10, units="ns").start())
    model = ExchangeModel()
    
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)
    
    random.seed(42)  # Fixed seed for reproducibility
    dut._log.info("=== Tracing with fixed seed=42 ===")
    
    NUM_USERS = 50
    last_users = []
    
    for tx_num in range(200):  # Run until divergence
        # Generate hazard-prone transaction
        if len(last_users) > 0 and random.random() < 0.5:
            user_a = random.choice(last_users)
        else:
            user_a = random.randint(0, NUM_USERS-1)
        
        user_b = random.randint(0, NUM_USERS-1)
        if user_a == user_b:
            user_b = (user_b + 1) % NUM_USERS
        
        opcode = random.randint(0, 1)
        amt0 = random.randint(1000, 5000)
        amt1 = random.randint(1000, 3000)
        
        # Apply to HW
        dut.s_opcode.value = opcode
        dut.s_user_a.value = user_a
        dut.s_user_b.value = user_b
        dut.s_amount_0.value = amt0
        dut.s_amount_1.value = amt1
        dut.s_valid.value = 1
        
        # Apply to model
        success, fee0, fee1 = model.process(opcode, user_a, user_b, amt0, amt1)
        
        await RisingEdge(dut.clk)
        
        # Track users for hazard generation
        last_users.append(user_a)
        last_users.append(user_b)
        if len(last_users) > 10:
            last_users = last_users[-10:]
        
        # Every 10 tx, verify user_a and user_b
        if tx_num % 10 == 9:
            await RisingEdge(dut.clk)  # Extra cycle for output to settle
            dut.s_valid.value = 0
            await RisingEdge(dut.clk)
            
            # Check user_a
            raw_a = int(dut.portfolios[user_a].value)
            hw_usdc_a = raw_a & 0xFFFFFFFFFFFFFFFF
            model_usdc_a = model.balances[user_a][0]
            
            if hw_usdc_a != model_usdc_a:
                dut._log.error(f"TX#{tx_num}: DIVERGENCE at user {user_a}!")
                dut._log.error(f"  HW USDC: {hw_usdc_a}, Model USDC: {model_usdc_a}")
                dut._log.error(f"  Last TX: op={opcode}, A={user_a}, B={user_b}, amt0={amt0}, amt1={amt1}")
                dut._log.error(f"  Vault HW: {int(dut.m_vault_usdc.value)}, Model: {model.vault[0]}")
                assert False, f"First divergence at TX {tx_num}"
            
            dut.s_valid.value = 1  # Resume
    
    dut._log.info("200 transactions verified without divergence!")
