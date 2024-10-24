TOPLEVEL_LANG ?= verilog
SIM := vcs

PWD=$(shell pwd)

export PYTHONPATH := $(PWD):$(PYTHONPATH)

VERILOG_SOURCES := $(PWD)/../multiplier.v
COMPILE_ARGS += +incdir+/home/mlm439/c2s2_ip/src #Include
COMPILE_ARGS += -cm line+tgl
COMPILE_ARGS += -sverilog
SIM_ARGS += -cm line+tgl
COCOTB_TOPLEVEL := FXPIterMultDatapath
MODULE := test_FXPIterMultDatapath
WAVES := 1


include /home/mlm439/cocotb/src/cocotb_tools/makefiles/Makefile.sim


