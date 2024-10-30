#HDL Language (always Verilog)
TOPLEVEL_LANG ?= verilog

#RTL Simulator (always Synopsys VCS)
SIM := vcs

#Add working directory to the Python virtual environment path
PWD=$(shell pwd)
export PYTHONPATH := $(PWD):$(PYTHONPATH)

#Add relative/full path of the Verilog file that contains the top level module to VERILOG_SOURCES
VERILOG_SOURCES = $(PWD)/../multiplier.v

#Add all include directories reference in the verilog source file
COMPILE_ARGS += +incdir+/home/mlm439/c2s2_ip/src #Include
TOPLEVEL = fixed_point_iterative_Multiplier
MODULE = test_fixed_point_iterative_Multiplier


#Generating waveforms (Set the variable WAVES to 1)
WAVES ?= 0
ifeq ($(WAVES), 1)
	EXTRA_ARGS += +vcs+dumpvars+waves.vcd
endif

#Generate line and toggle coverage data
COVER ?= 0
ifeq ($(COVER), 1)
	COMPILE_ARGS += -cm line+tgl
	SIM_ARGS += -cm line+tgl
endif

include $(shell cocotb-config --makefiles)/Makefile.sim

clean_all:
	rm -f waves.vcd
	make clean

coverage_report:
	urg -dir ./sim_build/simv.vdb -format both -report ./sim_build/coverage_report



