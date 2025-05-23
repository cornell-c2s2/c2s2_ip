#HDL Language (always Verilog)
TOPLEVEL_LANG ?= verilog

#RTL Simulator (always Synopsys VCS)
SIM := vcs

#Add working directory to the Python virtual environment path
PWD=$(shell pwd)
export PYTHONPATH := $(PWD):$(PYTHONPATH)

#Note: If working with functional models, make sure to UNCOMMENT the following line:

#export PYTHONPATH := $(PWD)/../models:$(PYTHONPATH)

#Step 1: Add relative/full path of the Verilog file that contains the top level module to VERILOG_SOURCES
VERILOG_SOURCES = $(PWD)/../lbist_toplevel.v

#Step 2: Add all include directories referenced in the verilog source file
COMPILE_ARGS += +incdir+$(PWD)/../../../

#Step 3: Set top level module and corresponding python test module
TOPLEVEL = lbist_toplevel 
# MODULE = cocotb_lbist_toplevel 
MODULE = demo

# send test build outputs to build folder
# SIM_BUILD = ../../build/convolution_block/iterative
# COCOTB_RESULTS_FILE = ../../build/convolution_block/iterative/results.xml

#Step 4: Set model parameters by adding them to EXTRA_ARGS \
using the following line as a reference:
#EXTRA_ARGS += +MY_PARAM=42

#Step 5: Set environment variables for waveforms and coverage data to 1 if you  \
would like either waveforms or coverage data to be produced by the simulation
WAVES = 1
COVER = 1

#Generating waveform files (Set environment variable WAVES to 1)
#Resulting waveform will be called waves.vcd and will be in the working directory
WAVES ?= 0
ifeq ($(WAVES), 1)
	EXTRA_ARGS += +vcs+dumpvars+waves.vcd
endif

#Generating line and toggle coverage data (Set environment variable COVER to 1)
COVER ?= 0
ifeq ($(COVER), 1)
	COMPILE_ARGS += -cm line+tgl
	SIM_ARGS += -cm line+tgl
endif

include $(shell cocotb-config --makefiles)/Makefile.sim

#Removing all files generated by a simulation
clean_all:
	rm -f waves.vcd
	rm -rf coverage_report
	make clean

#Generate a coverage report after running a simulation
coverage_report:
	urg -dir ./sim_build/simv.vdb -format both -report ./coverage_report
