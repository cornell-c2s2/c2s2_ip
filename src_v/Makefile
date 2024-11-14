TOP_DIR=$(shell git rev-parse --show-toplevel)
FPGA_DIR=$(TOP_DIR)/src_v
BUILD_DIR=$(TOP_DIR)/build

SCRIPT_DIR=$(FPGA_DIR)/scripts

# Make sure the pickled file exists
pickled_file = $(BUILD_DIR)/Interconnect_Fpga_noparam__pickled.v

# Temp helpers folder
temp_dir=$(FPGA_DIR)/helpers

all:
	@echo "Converting pickled file to Verilog..."
	@if [! test -f $(pickled_file)]; then \
		echo "Pickled file does not exist. Run 'pytest' on interconnect_fpga first."; \
		exit 1; \
	fi
	@mkdir -p $(temp_dir)
	@python3 $(SCRIPT_DIR)/sine_wave_lookup_generator.py 16 8 32

# @./scripts/convert.sh
# # @python3 scripts/extract.py $(INTER_FPGA_FILE) $(INTER_FPGA_EX_DIR)

# mostlyclean:
# 	@echo "Cleaning temporary Verilog files in $(TEMP_DIR)..."
# 	@find $(TEMP_DIR) -type f -name "*.v" | while read -r file; do \
#   		rm "$$file"; \
# 	done
# 	@echo "Done"

# clean:
# 	@echo "Cleaning Verilog files in FPGA and TEMP directories..."
# 	@find $(FPGA_DIR) -type f -name "*.v" | while read -r file; do \
# 		rm "$$file"; \
# 	done

	@find $(TEMP_DIR) -type f -name "*.v" | while read -r file; do \
		rm "$$file"; \
	done

	@echo "Done"
