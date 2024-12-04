TOP_DIR=$(shell git rev-parse --show-toplevel)
SRC_DIR=$(TOP_DIR)/src
FPGA_DIR=$(TOP_DIR)/src_v
BUILD_DIR=$(TOP_DIR)/src_v/build
SCRIPT_DIR=$(FPGA_DIR)/scripts

interconnect_file = $(SRC_DIR)/tapeins/sp24/tapein2/interconnect_fpga.v

# Make sure the pickled file exists
pickled_file = $(BUILD_DIR)/Interconnect_Fpga_pickled.v
lookup_file = $(BUILD_DIR)/sine_wave_lookup_16_8_32.v
	
all:
	@python $(SCRIPT_DIR)/sine_wave_lookup_generator.py 16 8 32 $(lookup_file)
	@python $(SCRIPT_DIR)/pickel.py --src $(SRC_DIR) \
					--interconnect $(interconnect_file) --out $(pickled_file)
	@python $(SCRIPT_DIR)/convert.py --vfile $(pickled_file) --lookup $(lookup_file)

	@echo "Done"
