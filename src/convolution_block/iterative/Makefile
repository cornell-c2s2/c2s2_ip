# Makefile

# defaults
SIM ?= icarus
TOPLEVEL_LANG ?= verilog

VERILOG_SOURCES += ./convolution_block_iterative.v
# use VHDL_SOURCES for VHDL files

VERILOG_INCLUDE_DIRS += ../../

# TOPLEVEL is the name of the toplevel module in your Verilog or VHDL file
TOPLEVEL = convolution_block_iterative_ConvolutionBlock 

# MODULE is the basename of the Python test file
MODULE = cocotb_convolution_iterative

# send test build outputs to build folder
SIM_BUILD = ../../build/iterative
COCOTB_RESULTS_FILE = ../../build/iterative.results.xml

# include cocotb's make rules to take care of the simulator setup
include $(shell cocotb-config --makefiles)/Makefile.sim