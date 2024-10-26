TOP_DIR=$(shell git rev-parse --show-toplevel)
FPGA_DIR=$(TOP_DIR)/src_v
TEMP_DIR=$(FPGA_DIR)/temp

INTER_FPGA_FILE=$(TOP_DIR)/src_v/temp/interconnect_fpga.v
INTER_FPGA_EX_DIR=$(TOP_DIR)/src_v
all:
	@./scripts/convert.sh
	# @python3 scripts/extract.py $(INTER_FPGA_FILE) $(INTER_FPGA_EX_DIR)

mostlyclean:
	@echo "Cleaning temporary Verilog files in $(TEMP_DIR)..."
	@find $(TEMP_DIR) -type f -name "*.v" | while read -r file; do \
  		rm "$$file"; \
	done
	@echo "Done"

clean:
	@echo "Cleaning Verilog files in FPGA and TEMP directories..."
	@find $(FPGA_DIR) -type f -name "*.v" | while read -r file; do \
		rm "$$file"; \
	done

	@find $(TEMP_DIR) -type f -name "*.v" | while read -r file; do \
		rm "$$file"; \
	done

	@echo "Done"
