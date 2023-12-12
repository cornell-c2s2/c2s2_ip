`default_nettype none
`include "wishbone/adder.v"

module wishbone_harnesses_AdderHarness 
(
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [31:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [31:0] send_msg
);

Adder adder (
  .clk(clk),
  .reset(reset),
  .i_stream_val(recv_val),
  .i_stream_rdy(recv_rdy),
  .i_stream_data(recv_msg),
  .o_stream_val(send_val),
  .o_stream_rdy(send_rdy),
  .o_stream_data(send_msg)
);



endmodule
