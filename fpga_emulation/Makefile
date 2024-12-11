TOP_DIR=$(shell git rev-parse --show-toplevel)
SRC_DIR=$(TOP_DIR)/src
FPGA_DIR=$(PWD)
BUILD_DIR=$(FPGA_DIR)/build
SCRIPT_DIR=$(FPGA_DIR)/scripts

# Conversion

interconnect_file = $(SRC_DIR)/tapeins/sp24/fpga_emulation2/interconnect_fpga.v

pickled_file = $(BUILD_DIR)/Interconnect_Fpga_pickled.v
lookup_file = $(BUILD_DIR)/sine_wave_lookup_16_8_32.v

# Quartus Programming: Requires updating depending on the installation path

qts_bin = ~/intelFPGA_lite/23.1std/quartus/bin/

QTS_SH = $(qts_bin)/quartus_sh
QTS_PGM = $(qts_bin)/quartus_pgm

convert:
	@mkdir -p $(BUILD_DIR)
	@python $(SCRIPT_DIR)/sine_wave_lookup_generator.py 16 8 32 $(lookup_file)
	@python $(SCRIPT_DIR)/pickel.py --src $(SRC_DIR) \
					--interconnect $(interconnect_file) --out $(pickled_file)
	@python $(SCRIPT_DIR)/convert.py --vfile $(pickled_file) --lookup $(lookup_file) \
					--out $(FPGA_DIR)/interconnect_fpga.v

	@echo "Done"

compile:
	@$(QTS_SH) -t emulation_sp24_tapein2.tcl

program:
	@$(QTS_PGM) -m JTAG -o "p;emulation_sp24_tapein2.sof@1"

all: convert compile program