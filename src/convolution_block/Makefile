# Makefile

# defaults
SIM ?= icarus
TOPLEVEL_LANG ?= verilog

VERILOG_SOURCES += $(PWD)/convolution_block.v
# use VHDL_SOURCES for VHDL files

VERILOG_INCLUDE_DIRS += ../

# TOPLEVEL is the name of the toplevel module in your Verilog or VHDL file
TOPLEVEL = convolution_block_ConvolutionBlock 

# MODULE is the basename of the Python test file
MODULE = cocotb_convolution

# send test build outputs to build folder
SIM_BUILD = ../../build
COCOTB_RESULTS_FILE = ../../build/results.xml

# include cocotb's make rules to take care of the simulator setup
include $(shell cocotb-config --makefiles)/Makefile.sim