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

  input  logic [2*BIT_WIDTH - 1:0] recv_msg,
  input  logic                     recv_val,
  output logic                     recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic                   send_val,
  input  logic                   send_rdy
);

  logic [BIT_WIDTH - 1:0] a;
  logic [BIT_WIDTH - 1:0] b;
  logic [BIT_WIDTH - 1:0] aProduct;
  logic [BIT_WIDTH - 1:0] bProduct;

  logic a_mult_recv_rdy;
  logic b_mult_recv_rdy;
  logic a_mult_send_val;
  logic b_mult_send_val;
  logic a_mult_send_rdy;
  logic b_mult_send_rdy;

  logic sqrt_recv_rdy;
  logic sqrt_recv_val;
  logic sqrt_send_val;

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
    .send_rdy(a_mult_send_rdy),
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
    .send_rdy(b_mult_send_rdy),
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
    .recv_val(sqrt_recv_val),
    .recv_rdy(sqrt_recv_rdy),

    .send_msg(send_msg),
    .send_val(sqrt_send_val),
    .send_rdy(send_rdy)
  );

  logic currentState, nextState;
  logic MULT = 1'b0, SQRT = 1'b1;

  always_comb begin
    case (currentState)
      MULT:
      if (a_mult_send_val && b_mult_send_val) nextState = SQRT;
      else nextState = MULT;
      SQRT:
      if (sqrt_send_val) nextState = MULT;
      else nextState = SQRT;
      default: nextState = MULT;
    endcase
  end

  always_comb begin
    case (currentState)
      MULT: begin
        recv_rdy = a_mult_recv_rdy && b_mult_recv_rdy;
        send_val = 0;
        a_mult_send_rdy = 1;
        b_mult_send_rdy = 1;
        sqrt_recv_val = 0;
      end

      SQRT: begin
        recv_rdy = 0;
        send_val = sqrt_send_val;
        a_mult_send_rdy = 0;
        b_mult_send_rdy = 0;
        sqrt_recv_val = 1;
      end

      default: begin
        recv_rdy = 0;
        send_val = 0;
        sqrt_recv_val = 0;
      end
    endcase
  end

  // State FFs
  always_ff @(posedge clk) begin
    if (reset) begin
      currentState <= MULT;
    end else begin
      currentState <= nextState;
    end
  end

endmodule
`endif
