
# ===============
# TODO Add section with env variables so users only need to change things in one area
# ===============


TOPLEVEL_LANG ?= verilog
SIM := vcs
# Adds working directory to python path
PWD=$(shell pwd)
export PYTHONPATH := $(PWD):$(PYTHONPATH)
VERILOG_SOURCES := $(PWD)/lfsr.v


# ===============
# COMPILE
# ===============
# Top level clone of c2s2.ip
# COMPILE_ARGS += +incdir+/home/jjm469/c2s2/misr/cocotb_test_example/cocotb_demo/src/ # Include all verilog files in c2s2_ip/src
COMPILE_ARGS += -cm line+tgl                     # Line and Toggle Coverage
COMPILE_ARGS += -sverilog                        # Flag to specify system verilog for VCS 

# ===============
# SIMULATION
# ===============
SIM_ARGS += -cm line+tgl                         # Line and Toggle Coverage

# Top level module to test
TOPLEVEL := lfsr

# Python test for top level module
MODULE := test_lfsr

# WAVES := 1  # Stale rn 

EXTRA_ARGS += +vcs+dumpvars+waves.vcd

# Including cocotb makefiles responsible for running simulation + compilation on desired simulator
include $(shell cocotb-config --makefiles)/Makefile.sim
