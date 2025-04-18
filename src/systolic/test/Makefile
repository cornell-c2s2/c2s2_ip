TOPLEVEL_LANG ?= verilog
SIM := vcs

PWD=$(shell pwd)
export PYTHONPATH := $(PWD):$(PYTHONPATH)

VERILOG_SOURCES=$(C2S2_PATH)/src/systolic/*.v

COMPILE_ARGS += +incdir+$(C2S2_PATH)/src
COMPILE_ARGS += -sverilog

WAVES=1
COVER=1

ifeq ($(WAVES), 1)
	EXTRA_ARGS += +vcs+dumpvars+waves.vcd
endif

ifeq ($(COVER), 1)
	COMPILE_ARGS += -cm line+tgl
	SIM_ARGS += -cm line+tgl
endif

include $(shell cocotb-config --makefiles)/Makefile.sim

clean_all:
	rm -f waves.vcd
	rm -rf coverage_report
	rm -f results.xml
	make clean

coverage_report:
	urg -dir ./sim_build/simv.vdb -format both -report ./coverage_report