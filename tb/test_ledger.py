import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
import sys
import os

# Import our Python Model
sys.path.append(os.path.join(os.path.dirname(__file__), "../model"))
from ledger_model import LedgerModel

@cocotb.test()
async def test_ledger_logic(dut):
    """
    Day 1 Test: Basic Logic + The Dreaded RAW Hazard
    """
    # 1. Setup
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    model = LedgerModel()

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("--- SCENARIO 1: Basic Transfer ---")
    # Agent 1 sends 50 to Agent 2
    # Expected: Agent 1 = 950, Agent 2 = 1050
    
    dut.s_payer.value = 1
    dut.s_payee.value = 2
    dut.s_amount.value = 50
    dut.s_valid.value = 1
    
    await RisingEdge(dut.clk)
    
    # Update Model
    model.process_transaction(1, 2, 50)
    
    # Clear Inputs
    dut.s_valid.value = 0
    
    # Wait for Pipeline (2 Cycles)
    await RisingEdge(dut.clk) 
    await RisingEdge(dut.clk)

    # Check Result
    if dut.m_valid.value == 1:
        hw_bal_payer = int(dut.m_bal_payer.value)
        hw_bal_payee = int(dut.m_bal_payee.value)
        
        assert hw_bal_payer == model.balances[1], f"Mismatch! HW: {hw_bal_payer}, Model: {model.balances[1]}"
        dut._log.info("Scenario 1 Passed! ✅")
    else:
        assert False, "Transaction 1 did not exit pipeline!"


    dut._log.info("--- SCENARIO 2: The RAW Hazard (Back-to-Back) ---")
    # Agent 1 sends 10 to Agent 3
    # Agent 1 sends 10 to Agent 4 (IMMEDIATELY AFTER)
    
    # Tx A
    dut.s_payer.value = 1
    dut.s_payee.value = 3
    dut.s_amount.value = 10
    dut.s_valid.value = 1
    await RisingEdge(dut.clk)
    model.process_transaction(1, 3, 10) # Model: Bal 1 goes 950 -> 940
    
    # Tx B (Immediate)
    dut.s_payer.value = 1
    dut.s_payee.value = 4
    dut.s_amount.value = 10
    dut.s_valid.value = 1
    await RisingEdge(dut.clk)
    model.process_transaction(1, 4, 10) # Model: Bal 1 goes 940 -> 930
    
    # Clear
    dut.s_valid.value = 0
    
    # Wait for Pipeline output of Tx B
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    
    # Check Result of Tx B
    hw_bal_payer = int(dut.m_bal_payer.value)
    expected_bal = model.balances[1]
    
    dut._log.info(f"Final Hardware Balance for Agent 1: {hw_bal_payer}")
    dut._log.info(f"Expected Model Balance for Agent 1: {expected_bal}")

    if hw_bal_payer != expected_bal:
        dut._log.error("HAZARD DETECTED! 🚨 The second transaction read stale data!")
        # We allow the test to fail here to prove the point
        assert False, "RAW Hazard Bug Found! (This is intentional for Day 1)"
    else:
        dut._log.info("Scenario 2 Passed! (Unexpected for V1 code)")

