SIM ?= verilator
TOPLEVEL_LANG ?= verilog
VERILOG_SOURCES += $(PWD)/../rtl/ledger_core.sv
TOPLEVEL = ledger_core
MODULE = test_ledger

# --assert: Enable SVA assertions
# --public: Allow Cocotb to read internal signals/memory (Crucial for the Swarm check)
EXTRA_ARGS += --assert --public

include $(shell cocotb-config --makefiles)/Makefile.sim
