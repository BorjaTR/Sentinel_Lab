import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__), "../model"))
from ledger_model import LedgerModel

@cocotb.test()
async def test_hazard_resolution(dut):
    """
    Day 2: Verify that the Forwarding Logic fixes the RAW Hazard.
    """
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    model = LedgerModel()

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    dut.s_valid.value = 0
    await RisingEdge(dut.clk)

    dut._log.info("--- STARTING HAZARD STRESS TEST ---")

    # Tx A: Agent 1 -> 2 (Amount 50)
    dut.s_payer.value = 1
    dut.s_payee.value = 2
    dut.s_amount.value = 50
    dut.s_valid.value = 1
    model.process_transaction(1, 2, 50) # Bal 1: 950
    await RisingEdge(dut.clk)

    # Tx B: Agent 1 -> 3 (Amount 50) - IMMEDIATE
    # This should now read 950 (forwarded), NOT 1000 (RAM)
    dut.s_payer.value = 1
    dut.s_payee.value = 3
    dut.s_amount.value = 50
    dut.s_valid.value = 1
    model.process_transaction(1, 3, 50) # Bal 1: 900
    await RisingEdge(dut.clk)

    # Clear
    dut.s_valid.value = 0
    
    # Wait for Pipeline
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)

    # Check Result of Tx B
    hw_bal = int(dut.m_bal_payer.value)
    model_bal = model.balances[1]

    dut._log.info(f"Hardware Balance: {hw_bal}")
    dut._log.info(f"Model Balance:    {model_bal}")

    if hw_bal == model_bal:
        dut._log.info("SUCCESS! 🛡️ Forwarding Logic prevented the double spend.")
    else:
        dut._log.error("FAILURE! 🚨 Hazard still exists.")
        assert False, f"Expected {model_bal}, Got {hw_bal}"
