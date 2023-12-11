//================================================
// a_maxb_min.v
//================================================
`default_nettype none
`ifndef A_MAXB_MIN_V
`define A_MAXB_MIN_V
`include "src/fixed_point/iterative/multiplier.v"

module AMaxbMin #(
  // Bit Width of Input (2 16-bit Fixed Point Numbers)
  parameter int BIT_WIDTH = 32,
  // Amount of Fractional Bits in Each Number
  parameter int F_BITS = 8
) (

  // Clock and Reset
  input logic clk,
  input logic reset,

  // val-rdy I/O
  output logic  recv_rdy,
  input logic   recv_val,
  input logic   [BIT_WIDTH - 1:0] recv_msg,
  input logic   send_rdy,
  output logic  send_val,
  output logic  [BIT_WIDTH / 2 - 1:0] send_msg
);
  // FSM Variables
  logic [1:0]   currentState;
  logic [1:0]   nextState;
  logic [1:0]   IDLE = 2'd0;
  logic [1:0]   CALC = 2'd1;
  logic [1:0]   DONE = 2'd3;

  // Multiplier Control
  logic [BIT_WIDTH / 2 - 1:0] aProduct;
  logic [BIT_WIDTH / 2 - 1:0] bProduct;
  logic                       a_mult_recv_rdy;
  logic                       b_mult_recv_rdy;
  logic                       a_mult_send_val;
  logic                       b_mult_send_val;

  // Alpha Multiplier
  FixedPointIterativeMultiplier #(
    .n                (BIT_WIDTH / 2),
    .d                (F_BITS),
    .sign             (0)
  )amult (
    .clk              (clk),
    .reset            (reset),
    .recv_val         (recv_val),
    .recv_rdy         (a_mult_recv_rdy),
    .a                (16'b0000000011110101),
    .b                (max),
    .send_rdy         (send_rdy),
    .send_val         (a_mult_send_val),
    .c                (aProduct)
  );

  // Beta Multiplier
  FixedPointIterativeMultiplier #(
    .n                (BIT_WIDTH / 2),
    .d                (BIT_WIDTH / 4),
    .sign             (0)
  ) bmult(
    .clk              (clk),
    .reset            (reset),
    .recv_val         (recv_val),
    .recv_rdy         (b_mult_recv_rdy),
    .a                (16'b0000000001100101),
    .b                (min),
    .send_rdy         (send_rdy),
    .send_val         (b_mult_send_val),
    .c                (bProduct)
  );

  // Find Max and Min
  logic [BIT_WIDTH - 1: 0] max;
  logic [BIT_WIDTH - 1: 0] min;
  always_comb begin
    if(recv_msg[BIT_WIDTH - 1: BIT_WIDTH / 2] >= recv_msg[BIT_WIDTH / 2 - 1: 0]) begin
      max = recv_msg[BIT_WIDTH - 1: BIT_WIDTH / 2];
      min = recv_msg[BIT_WIDTH / 2 - 1: 0];
    end else begin
      min = recv_msg[BIT_WIDTH - 1: BIT_WIDTH / 2];
      max = recv_msg[BIT_WIDTH / 2 - 1: 0];
    end
  end

  // Next State Logic
  always_comb begin
    case (currentState)
      IDLE:    if (recv_val && recv_rdy) nextState = CALC;
               else nextState = IDLE;
      CALC:    if (a_mult_send_val && b_mult_send_val) nextState = DONE;
               else nextState = CALC;
      DONE:    if (send_rdy && send_val) nextState = IDLE;
               else nextState = DONE;
      default: nextState = IDLE;
    endcase
  end

  // val-rdy Control Logic
  always_comb begin
    case(currentState)
      IDLE: begin
        recv_rdy = a_mult_recv_rdy && b_mult_recv_rdy;
        send_val = 0;
      end
      CALC: begin
        recv_rdy = 0;
        send_val = 0;
      end
      DONE: begin
        recv_rdy = 0;
        send_val = 1;
        send_msg = aProduct + bProduct;
      end
      default: begin
        recv_rdy = 'x;
        send_val = 'x;
      end
    endcase
  end

  // State FFs
  always_ff @(posedge clk) begin
    if (reset) begin
      currentState <= IDLE;
    end else begin
      currentState <= nextState;
    end
  end

endmodule
`endif
