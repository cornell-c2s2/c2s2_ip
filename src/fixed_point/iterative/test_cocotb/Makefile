TOPLEVEL_LANG ?= verilog
SIM := vcs

PWD=$(shell pwd)

export PYTHONPATH := $(PWD):$(PYTHONPATH)

VERILOG_SOURCES := $(PWD)/../multiplier.v
VCS_FLAGS += -debug_all
COMPILE_ARGS += +incdir+/home/mlm439/c2s2_ip/src #Include
COMPILE_ARGS += -cm line+tgl
COMPILE_ARGS += -sverilog
SIM_ARGS += -cm line+tgl
SIM_ARGS += +vcs+dumpvars+waveform.vcd
TOPLEVEL = FXPIterMultControl
MODULE = test_FXPIterMultControl


include $(shell cocotb-config --makefiles)/Makefile.sim


