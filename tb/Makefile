SIM ?= verilator
TOPLEVEL_LANG ?= verilog
VERILOG_SOURCES += $(PWD)/../rtl/ledger_core.sv
TOPLEVEL = ledger_core
MODULE = test_ledger

# --assert: Enable SVA assertions
# --public: Allow Cocotb to read internal signals/memory (Crucial for the Swarm check)
EXTRA_ARGS += --assert --public

# Hardcode cocotb path to avoid environment issues
# This works around Streamlit subprocess environment isolation
-include /usr/local/lib/python3.11/dist-packages/cocotb/share/makefiles/Makefile.sim
-include /usr/local/lib/python3.10/dist-packages/cocotb/share/makefiles/Makefile.sim
-include /usr/lib/python3/dist-packages/cocotb/share/makefiles/Makefile.sim
