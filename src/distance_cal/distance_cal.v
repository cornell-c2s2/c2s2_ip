//================================================
// distance_cal.v
//================================================
`default_nettype none
`ifndef DISTANCE_CAL
`define DISTANCE_CAL
`include "src/fixed_point/iterative/multiplier.v"
`include "src/a_maxb_min/fxp_sqrt.v"

module Distance_cal #(
  parameter int BIT_WIDTH = 32,
  parameter int F_BITS = 16
) (
  input logic reset,
  input logic clk,

  input  logic [BIT_WIDTH - 1:0] a,
  input  logic [BIT_WIDTH - 1:0] b,
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic                   send_val,
  input  logic                   send_rdy
);

  logic [BIT_WIDTH-1:0] aProduct;
  logic [BIT_WIDTH-1:0] bProduct;

  logic sqrt_recv_rdy;
  logic a_mult_send_val;
  logic b_mult_send_val;

  FixedPointIterativeMultiplier #(
    .n(BIT_WIDTH),
    .d(F_BITS),
    .sign(0)
  ) amult (
    .clk(clk),
    .reset(reset),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .a(a),
    .b(a),
    .send_rdy(sqrt_recv_rdy),
    .send_val(a_mult_send_val),
    .c(aProduct)
  );

  FixedPointIterativeMultiplier #(
    .n(BIT_WIDTH),
    .d(F_BITS),
    .sign(0)
  ) bmult (
    .clk(clk),
    .reset(reset),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .a(b),
    .b(b),
    .send_rdy(sqrt_recv_rdy),
    .send_val(b_mult_send_val),
    .c(bProduct)
  );

  // ========================================
  // Square root
  // ========================================
  logic [BIT_WIDTH-1:0] added;
  assign added = aProduct + bProduct;

  Fxp_sqrt #(
    .BIT_WIDTH(BIT_WIDTH),
    .F_BITS(F_BITS)
  ) sqrt (
    .clk  (clk),
    .reset(reset),

    .recv_msg(added),
    .recv_val(b_mult_send_val && a_mult_send_val),
    .recv_rdy(sqrt_recv_rdy),

    .send_msg(send_msg),
    .send_val(send_val),
    .send_rdy(send_rdy)
  );

endmodule
`endif
