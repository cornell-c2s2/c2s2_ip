`default_nettype none
`include "src/wishbone/wishbone.v"

module WishboneHarness #(
  parameter int n_modules = 1
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [73+2*n_modules-1:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [33+2*n_modules-1:0] send_msg
);

Wishbone #(n_modules) wb (
  //inputs
  .i_stream_rdy(recv_msg[73+2*n_modules-1:73+n_modules]),
  .i_stream_val(recv_msg[73+n_modules-1:73]),
  .wb_clk_i(recv_msg[72]),
  .wb_rst_i(recv_msg[71]),
  .wbs_stb_i(recv_msg[70]),
  .wbs_cyc_i(recv_msg[69]),
  .wbs_we_i(recv_msg[68]),
  .wbs_sel_i(recv_msg[67:64]),
  .wbs_dat_i(recv_msg[63:32]),
  .wbs_adr_i(recv_msg[31:0]),
  //outputs
  .o_stream_rdy(send_msg[33+2*n_modules-1:33+n_modules]),
  .o_stream_val(send_msg[33+n_modules-1:33]),
  .wbs_ack_o(send_msg[32]),
  .wbs_dat_o(send_msg[31:0])
);

endmodule
