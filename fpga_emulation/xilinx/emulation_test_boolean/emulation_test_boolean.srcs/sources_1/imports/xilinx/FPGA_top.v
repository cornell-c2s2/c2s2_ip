module FPGA_top (
	input wire        clk,
	inout wire        JA1,
  inout wire        JA2,
  inout wire        JA3,
  inout wire        JA4,
  inout wire        JA7, // reset GPIO
	output logic [1:0] led
);

assign led[0] = JA7;
assign led[1] = ~JA7;

tapeins_sp24_fpga_emulation2_Interconnect_Fpga dut(
  .clk            (clk),
  .reset          (JA7),
  .cs             (JA4),
  .mosi           (JA3),
  .miso           (JA2),
  .sclk           (JA1),
  .minion_parity  (),
  .adapter_parity ()
);

endmodule