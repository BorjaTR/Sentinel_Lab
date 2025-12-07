SIM ?= verilator
TOPLEVEL_LANG ?= verilog
VERILOG_SOURCES += $(PWD)/../rtl/ledger_core.sv
TOPLEVEL = ledger_core
MODULE = test_ledger

# --assert: Enable SVA assertions
# --public: Allow Cocotb to read internal signals/memory (Crucial for the Swarm check)
EXTRA_ARGS += --assert --public

# Support COCOTB_MAKEFILES env var to avoid needing cocotb-config binary
# This is critical for environments (like Streamlit) where cocotb-config isn't accessible
ifdef COCOTB_MAKEFILES
include $(COCOTB_MAKEFILES)/Makefile.sim
else
include $(shell cocotb-config --makefiles)/Makefile.sim
endif
