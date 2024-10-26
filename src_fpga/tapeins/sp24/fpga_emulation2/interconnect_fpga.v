//======================================================================
// FPGA Emulation Top Module
//======================================================================
`include "tapeins/sp24/tapein2/interconnect2.v"

module tapeins_sp24_fpga_emulation2_Interconnect_Fpga (
  input  logic clk,
  input  logic reset,
  input  logic cs,
  input  logic mosi,
  output logic miso,
  input  logic sclk,
  output logic minion_parity,
  output logic adapter_parity
);

  // Connections for unused Wishbone inputs and outputs
  logic wbs_stb_i;
  logic wbs_cyc_i;
  logic wbs_we_i;
  logic [3:0] wbs_sel_i;
  logic [31:0] wbs_dat_i;
  logic [31:0] wbs_adr_i;
  logic wbs_ack_o;
  logic [31:0] wbs_dat_o;
  logic [22:0] io_oeb;
  logic [4:0] io_out;

  tapeins_sp24_tapein2_Interconnect2 interconnect_top (
    // SPI Connections
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .mosi(mosi),
    .miso(miso),
    .sclk(sclk),
    .minion_parity(minion_parity),
    .adapter_parity(adapter_parity),

    // Wishbone Connections
    .wbs_stb_i(wbs_stb_i),
    .wbs_cyc_i(wbs_cyc_i),
    .wbs_we_i (wbs_we_i),
    .wbs_sel_i(wbs_sel_i),
    .wbs_dat_i(wbs_dat_i),
    .wbs_adr_i(wbs_adr_i),
    .wbs_ack_o(wbs_ack_o),
    .wbs_dat_o(wbs_dat_o),

    .io_oeb(io_oeb),
    .io_out(io_out)
  );

  // Set wishbone inputs to zero.
  assign wbs_stb_i = 1'b0;
  assign wbs_cyc_i = 1'b0;
  assign wbs_we_i  = 1'b0;
  assign wbs_sel_i = 4'b0;
  assign wbs_dat_i = 32'b0;
  assign wbs_adr_i = 32'b0;

  // Attach wishbone outputs to unused wires.
  wire unused_wbs_ack_o;
  wire unused_wbs_dat_o;
  wire unused_io_oeb;
  wire unused_io_out;

  assign unused_wbs_ack_o = wbs_ack_o;
  assign unused_wbs_dat_o = &wbs_dat_o;
  assign unused_io_oeb = &io_oeb;
  assign unused_io_out = &io_out;

endmodule
