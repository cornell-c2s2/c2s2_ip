module FPGA_top (
	input logic CLOCK_50,
	input logic KEY0,
	inout logic GPIO0,
	inout logic GPIO2,
	inout logic GPIO4,
	inout logic GPIO6

);

tapeins_sp24_fpga_emulation2_Interconnect_Fpga dut(
  .clk(CLOCK_50),
  .reset(~KEY0),
  .cs(GPIO6),
  .mosi(GPIO4),
  .miso(GPIO2),
  .sclk(GPIO0),
  .minion_parity(),
  .adapter_parity()
);

endmodule