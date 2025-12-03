import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import sys
import os
import random

sys.path.append(os.path.join(os.path.dirname(__file__), "../model"))
from ledger_model import LedgerModel

@cocotb.test()
async def test_agent_swarm(dut):
    """
    Day 3: The Agent Swarm (Batch Mode)
    Inject 5,000 random transactions back-to-back.
    Verify FINAL state consistency to prove no money was lost.
    """
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    model = LedgerModel()

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("--- 🚀 LAUNCHING AGENT SWARM (5,000 TXs) ---")

    # 1. INJECTION PHASE
    for i in range(5000):
        payer = random.randint(0, 1023)
        payee = random.randint(0, 1023)
        amount = random.randint(1, 100) 

        dut.s_payer.value = payer
        dut.s_payee.value = payee
        dut.s_amount.value = amount
        dut.s_valid.value = 1

        # Keep model in sync
        model.process_transaction(payer, payee, amount)

        await RisingEdge(dut.clk)

    # 2. COOLDOWN PHASE
    dut.s_valid.value = 0
    for _ in range(10): # Wait for pipeline to drain
        await RisingEdge(dut.clk)

    # 3. VERIFICATION PHASE (Backdoor Read)
    # We read the internal RAM directly to verify the final state.
    dut._log.info("--- 🛑 SWARM COMPLETE. VERIFYING LEDGER... ---")
    
    errors = 0
    for i in range(1024):
        # Access internal signal: dut.balances
        hw_bal = int(dut.balances[i].value)
        exp_bal = model.balances[i]
        
        if hw_bal != exp_bal:
            dut._log.error(f"❌ User {i}: HW {hw_bal} != Model {exp_bal}")
            errors += 1
            
    if errors == 0:
        dut._log.info(f"✅ SUCCESS: All 1,024 accounts match perfectly after 5,000 high-speed trades.")
        dut._log.info(f"🛡️  Zero Forwarding Errors Detected.")
    else:
        assert False, f"Ledger corrupted! {errors} account mismatches found."
