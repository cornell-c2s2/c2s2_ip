`default_nettype none
`include "src/wishbone/wishbone.v"

module WishboneHarness #(
  parameter int n_modules = 1
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [103+2*n_modules-1:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [65+2*n_modules-1:0] send_msg
);
assign recv_rdy = 1;
assign send_val = 1;

Wishbone #(n_modules) wb (
  //inputs
  .clk(clk),
  .reset(reset),
  .i_stream_rdy(recv_msg[103+2*n_modules-1:103+n_modules]),
  .o_stream_val(recv_msg[103+n_modules-1:103]),
  .wbs_stb_i(recv_msg[102]),
  .wbs_cyc_i(recv_msg[101]),
  .wbs_we_i(recv_msg[100]),
  .wbs_sel_i(recv_msg[99:96]),
  .o_stream_data(recv_msg[95:64]),
  .wbs_dat_i(recv_msg[63:32]),
  .wbs_adr_i(recv_msg[31:0]),
  //outputs
  .o_stream_rdy(send_msg[65+2*n_modules-1:65+n_modules]),
  .i_stream_val(send_msg[65+n_modules-1:65]),
  .wbs_ack_o(send_msg[64]),
  .i_stream_data(send_msg[63:32]),
  .wbs_dat_o(send_msg[31:0])
);

endmodule
