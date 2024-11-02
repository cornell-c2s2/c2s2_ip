module FPGA_top (
	input logic CLOCK_50,
	inout logic GPIO0,
	input logic GPIO1,
	inout logic GPIO2,
	inout logic GPIO4,
	inout logic GPIO6,
	output logic LEDR0,
	output logic LEDR1
);

assign LEDR0 = GPIO1;
assign LEDR1 = ~GPIO1;

tapeins_sp24_fpga_emulation2_Interconnect_Fpga dut(
  .clk(CLOCK_50),
  .reset(GPIO1),
  .cs(GPIO6),
  .mosi(GPIO4),
  .miso(GPIO2),
  .sclk(GPIO0),
  .minion_parity(),
  .adapter_parity()
);

endmodule