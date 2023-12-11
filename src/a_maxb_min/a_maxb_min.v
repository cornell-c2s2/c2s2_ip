//================================================
// a_maxb_min.v
//================================================
`default_nettype none
`ifndef A_MAXB_MIN_V
`define A_MAXB_MIN_V
`include "src/fixed_point/iterative/multiplier.v"
`include "src/a_maxb_min/fxp_sqrt.v"

module AMaxbMin #(
  parameter int BIT_WIDTH = 32,
  parameter int F_BITS = 16
) (
  input logic clk,
  input logic reset,

  output logic recv_rdy,
  input logic recv_val,
  input logic [2*BIT_WIDTH - 1:0] recv_msg,

  input logic send_rdy,
  output logic send_val,
  output logic [BIT_WIDTH  - 1:0] send_msg
);

  logic [1:0] currentState;
  logic [1:0] nextState;
  logic [1:0] IDLE = 2'd0, CALC = 2'd1, DONE = 2'd3;

  logic [BIT_WIDTH - 1:0] a;
  logic [BIT_WIDTH - 1:0] b;
  logic [BIT_WIDTH - 1:0] aProduct;
  logic [BIT_WIDTH - 1:0] bProduct;

  logic a_mult_recv_rdy;
  logic b_mult_recv_rdy;
  logic a_mult_send_val;
  logic b_mult_send_val;

  logic sqrt_recv_rdy;

  assign a = recv_msg[2*BIT_WIDTH-1 : BIT_WIDTH];
  assign b = recv_msg[BIT_WIDTH-1 : 0];

  FixedPointIterativeMultiplier #(
    .n(BIT_WIDTH),
    .d(F_BITS),
    .sign(0)
  ) amult (
    .clk(clk),
    .reset(reset),
    .recv_val(recv_val),
    .recv_rdy(a_mult_recv_rdy),
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
    .recv_rdy(b_mult_recv_rdy),
    .a(b),
    .b(b),
    .send_rdy(sqrt_recv_rdy),
    .send_val(b_mult_send_val),
    .c(bProduct)
  );
  // logic [BIT_WIDTH - 1:0] max;
  // logic [BIT_WIDTH - 1:0] min;


  // always_comb begin
  //   case (currentState)
  //     IDLE:    if (recv_val && recv_rdy) nextState = CALC;
  //              else nextState = IDLE;
  //     CALC:    if (1) nextState = DONE;
  //              else nextState = CALC;
  //     DONE:    if (send_rdy && send_val) nextState = IDLE;
  //              else nextState = DONE;
  //     default: nextState = IDLE;
  //   endcase
  // end

  // always_comb begin
  //   case (currentState)
  //     IDLE: begin
  //       recv_rdy = a_mult_recv_rdy && b_mult_recv_rdy;
  //       send_val = 0;
  //     end

  //     CALC: begin
  //       recv_rdy = 0;
  //       send_val = 0;
  //     end

  //     DONE: begin
  //       recv_rdy = 0;
  //     end

  //     default: begin
  //       recv_rdy = 'x;
  //       send_val = 'x;
  //     end
  //   endcase
  // end

  // // State FFs
  // always_ff @(posedge clk) begin
  //   if (reset) begin
  //     currentState <= IDLE;
  //   end else begin
  //     currentState <= nextState;
  //   end
  // end


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
