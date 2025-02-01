`include "../src/tapeins/sp24/fpga_emulation2/interconnect_fpga.v"

module FPGA_top (
	input logic        clk,
	inout logic        JD1,
  inout logic        JD2,
  inout logic        JD3,
  inout logic        JD4,
  inout logic        JD7, // reset GPIO
	output logic [1:0] LED
);

assign LED[0] = JD7;
assign LED[1] = ~JD7;

tapeins_sp24_fpga_emulation2_Interconnect_Fpga dut(
  .clk            (clk),
  .reset          (JD7),
  .cs             (JD4),
  .mosi           (JD3),
  .miso           (JD2),
  .sclk           (JD1),
  .minion_parity  (),
  .adapter_parity ()
);

endmodule