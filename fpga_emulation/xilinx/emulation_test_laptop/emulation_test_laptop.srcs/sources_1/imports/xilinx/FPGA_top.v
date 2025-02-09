module FPGA_top (
	input wire        clk,
	inout wire        JD1,
  inout wire        JD2,
  inout wire        JD3,
  inout wire        JD4,
  inout wire        JD7, // reset GPIO
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