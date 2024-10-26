module FPGA_top (
	input logic CLOCK_50,
	input logic KEY0,
	inout logic [4:0] GPIO
);

tapeins_sp24_fpga_emulation2_Interconnect_Fpga dut(
  .clk(CLOCK_50),
  .reset(~KEY0),
  .cs(GPIO[0]),
  .mosi(GPIO[1]),
  .miso(GPIO[2]),
  .sclk(GPIO[3]),
  .minion_parity(),
  .adapter_parity()
);

endmodule