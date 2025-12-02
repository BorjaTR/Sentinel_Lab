SIM ?= verilator
TOPLEVEL_LANG ?= verilog
VERILOG_SOURCES += $(PWD)/../rtl/ledger_core.sv
TOPLEVEL = ledger_core
MODULE = test_ledger
include $(shell cocotb-config --makefiles)/Makefile.sim
