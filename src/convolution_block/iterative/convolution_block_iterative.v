//================================================
// convolution_block.v
//================================================
`default_nettype none
`ifndef iterative_CONVOLUTION_BLOCK_V
`define iterative_CONVOLUTION_BLOCK_V

`include "fixed_point/iterative/multiplier.v"

module convolution_block_iterative_ConvolutionBlock #(
  parameter int BIT_WIDTH = 32,
  parameter int ARRAY_LENGTH = 8
) (
  input logic clk,
  input logic reset,

  // input array
  output logic input_rdy,
  input logic input_val,
  input logic [BIT_WIDTH - 1:0] input_msg[ARRAY_LENGTH - 1:0],

  // input filter
  output logic filter_rdy,
  input logic filter_val,
  input logic [BIT_WIDTH - 1:0] filter_msg[ARRAY_LENGTH - 1:0],

  // output array
  input logic output_rdy,
  output logic output_val,
  output logic [BIT_WIDTH - 1:0] output_msg[ARRAY_LENGTH - 1:0]
);
  logic [1:0] IDLE = 2'd0, CALC = 2'd1, DONE = 2'd2;
  logic [1:0] state, next_state;

  logic [ARRAY_LENGTH - 1:0] recv_rdy_bus;
  logic [ARRAY_LENGTH - 1:0] send_val_bus;

  // manage state
  always_comb begin
    case (state)
      IDLE: begin
        if (input_val && filter_val) next_state = CALC;
        else next_state = IDLE;
      end
      CALC: begin
        if (&send_val_bus) next_state = DONE;
        else next_state = CALC;
      end
      DONE: begin
        if (output_rdy) next_state = IDLE;
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
        input_rdy  = 1;
        filter_rdy = 1;
        output_val = 0;
      end
      CALC: begin
        input_rdy  = 0;
        filter_rdy = 0;
        output_val = 0;
      end
      DONE: begin
        input_rdy  = 0;
        filter_rdy = 0;
        output_val = 1;
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

  // perform array convolution: output[i] = input[i] * filter[n - i]
  generate
    for (genvar i = 0; i < ARRAY_LENGTH; i++) begin
      fixed_point_iterative_Multiplier #(BIT_WIDTH, 0, 0) mult (
        .clk(clk),
        .reset(reset),
        .recv_rdy(recv_rdy_bus[i]),
        .recv_val(input_val & filter_val),
        .a(input_msg[i]),
        .b(filter_msg[ARRAY_LENGTH-i-1]),
        .send_rdy(output_rdy),
        .send_val(send_val_bus[i]),
        .c(output_msg[i])
      );
    end
  endgenerate
endmodule

`endif
