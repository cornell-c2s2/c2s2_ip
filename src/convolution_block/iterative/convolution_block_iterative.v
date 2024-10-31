//================================================
// convolution_block.v
//================================================
`default_nettype none
`ifndef iterative_CONVOLUTION_BLOCK_V
`define iterative_CONVOLUTION_BLOCK_V

`include "fixed_point/iterative/multiplier.v"

module convolution_block_iterative_ConvolutionBlock #(
  parameter int BIT_WIDTH = 32,
  parameter int ARRAY_LENGTH = 8,
  parameter int DECIMAL_BITS = 0,
  parameter bit SIGN = 1
) (
  input  logic clk,
  input  logic reset,

  // input array
  output logic req1_rdy,
  input  logic req1_val,
  input  logic [BIT_WIDTH - 1:0] req1_msg[ARRAY_LENGTH - 1:0],

  // input filter (array that gets reversed)
  output logic req2_rdy,
  input  logic req2_val,
  input  logic [BIT_WIDTH - 1:0] req2_msg[ARRAY_LENGTH - 1:0],

  // output array
  input  logic resp_rdy,
  output logic resp_val,
  output logic [BIT_WIDTH - 1:0] resp_msg[ARRAY_LENGTH - 1:0]
);
  localparam IDLE = 2'd0, CALC = 2'd1, DONE = 2'd2;
  logic [1:0] state, next_state;

  logic [ARRAY_LENGTH - 1:0] send_val_bus;
  logic [ARRAY_LENGTH - 1:0] recv_rdy_bus;

  // manage state
  always_comb begin
    case (state)
      IDLE: begin
        if (req1_val && req2_val && &recv_rdy_bus) next_state = CALC;
        else next_state = IDLE;
      end
      CALC: begin
        if (&send_val_bus) next_state = DONE;
        else next_state = CALC;
      end
      DONE: begin
        if (resp_rdy) next_state = IDLE;
        else next_state = DONE;
      end
      default: begin
        next_state = IDLE;
      end
    endcase
  end

  // manage data path
  always_comb begin
    case (state)
      IDLE: begin
        req1_rdy = 1;
        req2_rdy = 1;
        resp_val = 0;
      end
      CALC: begin
        req1_rdy = 0;
        req2_rdy = 0;
        resp_val = 0;
      end
      DONE: begin
        req1_rdy = 0;
        req2_rdy = 0;
        resp_val = 1;
      end
      default: begin
      end
    endcase
  end

  // reset logic
  always_ff @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  // perform array convolution: resp[i] = req1[i] * req2[n - i]
  generate
    for (genvar i = 0; i < ARRAY_LENGTH; i++) begin
      fixed_point_iterative_Multiplier #(BIT_WIDTH, DECIMAL_BITS, SIGN) mult (
        .clk(clk),
        .reset(reset),
        .recv_rdy(recv_rdy_bus[i]),
        .recv_val(req1_val & req2_val),
        .a(req1_msg[i]),
        .b(req2_msg[ARRAY_LENGTH-i-1]),
        .send_rdy(resp_rdy),
        .send_val(send_val_bus[i]),
        .c(resp_msg[i])
      );
    end
  endgenerate
endmodule

`endif
