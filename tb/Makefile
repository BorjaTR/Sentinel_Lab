# Makefile for Sentinel Core

# Use Verilator as the simulator
SIM ?= verilator

# Language is Verilog/SystemVerilog
TOPLEVEL_LANG ?= verilog

# Point to the RTL file we just made
VERILOG_SOURCES += $(PWD)/../rtl/ledger_core.sv

# The name of the module inside the .sv file
TOPLEVEL = ledger_core

# The name of the Python file (without .py)
MODULE = test_ledger

# Include the standard Cocotb rules
include $(shell cocotb-config --makefiles)/Makefile.sim
