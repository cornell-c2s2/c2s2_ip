TOPLEVEL_LANG ?= verilog
VERILOG_SOURCES=../hw/*.v

WAVES=1
COVER=1

include $(shell cocotb-config --makefiles)/Makefile.sim

clean_all:
	rm -f waves.vcd
	rm -rf coverage_report
	rm -f results.xml
	make clean

coverage_report:
	urg -dir ./sim_build/simv.vdb -format both -report ./coverage_report
