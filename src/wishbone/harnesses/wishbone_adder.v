`default_nettype none
`include "src/wishbone/adder.v"
`include "src/wishbone/wishbone.v"

module AdderHarness 
(
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [69:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [32:0] send_msg
);
//recv_msg
//     69          68        67       66:64      63:32     31:0
//+-----------+---------+---------+---------+----------+-----------+
// wbs_stb_i  wbs_cyc_i  wbs_we_i  wbs_sel_i  wbs_dat_i  wbs_adr_i


//resp_msg
//    32         31:0
//+-----------+---------+
//  wbs_ack_o  wbs_dat_o

// wb -> adder
logic c_i_stream_val;
logic [31:0] c_i_stream_data;
logic c_o_stream_rdy;

// adder -> wb
logic c_i_stream_rdy;
logic [31:0] c_o_stream_data;
logic c_o_stream_val;

Wishbone #(1) wb (
  //inputs
  .clk(clk),
  .reset(reset),

  //proc ->  wb
  .wbs_stb_i(recv_msg[102]),
  .wbs_cyc_i(recv_msg[101]),
  .wbs_we_i(recv_msg[100]),
  .wbs_sel_i(recv_msg[99:96]),
  .wbs_dat_i(recv_msg[63:32]),
  .wbs_adr_i(recv_msg[31:0]),


  //wb -> proc
  .wbs_ack_o(send_msg[64]),
  .wbs_dat_o(send_msg[31:0]),

  //wb -> adder
  .i_stream_val(send_msg[65+n_modules-1:65]),
  .i_stream_data(send_msg[63:32]),
  .o_stream_rdy(send_msg[65+2*n_modules-1:65+n_modules]),

  //adder -> wb
  .i_stream_rdy(),
  .o_stream_val(),
  .o_stream_data()

);

Adder adder (
  .clk(clk),
  .reset(reset),

  // inputs
  .i_stream_val(recv_val),
  .i_stream_data(recv_msg),
  .o_stream_rdy(send_rdy),

  // outputs
  .i_stream_rdy(recv_rdy),
  .o_stream_val(send_val),
  .o_stream_data(send_msg)
);



endmodule
