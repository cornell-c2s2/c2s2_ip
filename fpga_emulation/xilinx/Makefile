TOP_DIR=$(shell git rev-parse --show-toplevel)
SRC_DIR=$(TOP_DIR)/src
FPGA_DIR=$(PWD)
BUILD_DIR=$(FPGA_DIR)/build
SCRIPT_DIR=$(TOP_DIR)/fpga_emulation/scripts

# Conversion
src_emulation_dir = $(SRC_DIR)/tapeins/sp24/fpga_emulation2
interconnect_file = $(src_emulation_dir)/interconnect_fpga.v

# Output files
pickled_file = $(BUILD_DIR)/Interconnect_Fpga_pickled.v
lookup_file = $(BUILD_DIR)/sine_wave_lookup_16_8_32.v
interconnect_out = $(FPGA_DIR)/interconnect_fpga.v

# Quartus output files/directories
qpf_out = $(FPGA_DIR)/*.qpf
qsf_out = $(FPGA_DIR)/*.qsf
db_dir = $(FPGA_DIR)/db
incr_db_dir = $(FPGA_DIR)/incremental_db
log_dir = $(FPGA_DIR)/log
output_files_dir = $(FPGA_DIR)/output_files

# Quartus Programming: Requires updating depending on the installation path

# qts_bin = ~/intelFPGA_lite/23.1std/quartus/bin/

# QTS_SH = $(qts_bin)/quartus_sh
# QTS_PGM = $(qts_bin)/quartus_pgm

convert:
	@mkdir -p $(BUILD_DIR)
	@python $(SCRIPT_DIR)/sine_wave_lookup_generator.py 16 8 32 $(lookup_file)
	@python $(SCRIPT_DIR)/pickle.py --src $(SRC_DIR) \
					--interconnect $(interconnect_file) --out $(pickled_file)
	@python $(SCRIPT_DIR)/convert_xilinx.py --vfile $(pickled_file) --lookup $(lookup_file) \
					--out $(interconnect_out)

	@echo "Done"

# compile:
# 	@$(QTS_SH) -t emulation_sp24_tapein2.tcl

# program:
# 	@$(QTS_PGM) -m JTAG -o "p;output_files/emulation_sp24_tapein2.sof@1"

# clean:
# 	@echo "Cleaning up..."
# 	@rm -rf $(BUILD_DIR)
# 	@rm -f $(interconnect_out)
# 	@rm -f $(qpf_out) $(qsf_out) $(db_dir) 
# 	@rm -rf $(incr_db_dir) $(log_dir) $(output_files_dir)

all: convert #compile program