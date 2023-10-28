//================================================
// wishbone.v
//================================================
`default_nettype none
`ifndef WISHBONE_V
`define WISHBONE_V

module Wishbone  #(
  parameter n_modules = 1
)
  (
  // Wishbone Slave ports (WB MI A)
  input logic [n_modules-1:0] i_stream_rdy,
  input logic [n_modules-1:0] i_stream_val,

  input logic wb_clk_i,
  input logic wb_rst_i,
  input logic wbs_stb_i,
  input logic wbs_cyc_i,
  input logic wbs_we_i,
  input logic [3:0] wbs_sel_i,
  input logic [31:0] wbs_dat_i,
  input logic [31:0] wbs_adr_i,

  output logic [n_modules-1:0] o_stream_rdy,
  output logic [n_modules-1:0] o_stream_val,

  output logic wbs_ack_o,
  output logic [31:0] wbs_dat_o

);

  localparam   [31:0]  BASE_ADDRESS    = 32'h3000_0000;        // base address
  localparam   [31:0]  FFT_ADDRESS     = BASE_ADDRESS+4;
  assign wbs_dat_o = 32'b0;
endmodule

`endif
