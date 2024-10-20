//================================================
// convolution_block.v
//================================================
`default_nettype none
`ifndef CONVOLUTION_BLOCK_V
`define CONVOLUTION_BLOCK_V

module convolution_block_ConvolutionBlock #(
  parameter int BIT_WIDTH = 32,
  parameter int ARRAY_LENGTH = 8
) (
  input logic clk,
  input logic reset,

  // input array
  output logic input_arr_rdy,
  input logic input_arr_val,
  input logic [BIT_WIDTH - 1:0] input_arr_msg[ARRAY_LENGTH - 1:0],

  // input filter
  output logic filter_rdy,
  input logic filter_val,
  input logic [BIT_WIDTH - 1:0] filter_msg[ARRAY_LENGTH - 1:0],

  // output array
  input logic output_arr_rdy,
  output logic output_arr_val,
  output logic [BIT_WIDTH - 1:0] output_arr_msg[ARRAY_LENGTH - 1:0]
);

  // assign val and rdy bits
  always @(posedge clk) begin
    input_arr_rdy = output_arr_rdy;
    filter_rdy = output_arr_rdy;
    output_arr_val = input_arr_val & filter_val;
  end

  // perform array convolution: output[i] = input[i] * filter[n - i]
  generate
    for (genvar i = 0; i < ARRAY_LENGTH; i++) begin
      always @(posedge clk) begin
        output_arr_msg[i] <= reset ? 0 : input_arr_msg[i] * filter_msg[ARRAY_LENGTH-i-1];
      end
    end
  endgenerate
endmodule

`endif
