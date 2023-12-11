`default_nettype none
`include "src/distance_cal/distance_cal.v"

module HarnessDCal #(
  parameter int BIT_WIDTH = 32,
  parameter int F_BITS = 16
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [2*BIT_WIDTH-1:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [BIT_WIDTH-1:0] send_msg
);

  Distance_cal #(BIT_WIDTH, F_BITS) DCal (
    .clk  (clk),
    .reset(reset),

    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .a(recv_msg[2*BIT_WIDTH-1:BIT_WIDTH]),
    .b(recv_msg[BIT_WIDTH-1:0]),

    .send_val(send_val),
    .send_rdy(send_rdy),
    .send_msg(send_msg)
  );

endmodule
