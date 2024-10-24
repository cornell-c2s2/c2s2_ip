//================================================
// convolution_block.v
//================================================
`default_nettype none
`ifndef combinational_CONVOLUTION_BLOCK_V
`define combinational_CONVOLUTION_BLOCK_V

module convolution_block_combinational_ConvolutionBlock #(
  parameter int BIT_WIDTH = 32,
  parameter int ARRAY_LENGTH = 8
) (
  input logic clk,
  input logic reset,

  // input array
  input logic [BIT_WIDTH - 1:0] input_msg[ARRAY_LENGTH - 1:0],

  // input filter
  input logic [BIT_WIDTH - 1:0] filter_msg[ARRAY_LENGTH - 1:0],

  // output array
  output logic [BIT_WIDTH - 1:0] output_msg[ARRAY_LENGTH - 1:0]
);

  // perform array convolution: output[i] = input[i] * filter[n - i]
  generate
    for (genvar i = 0; i < ARRAY_LENGTH; i++) begin
      always @(posedge clk) begin
        output_msg[i] <= reset ? 0 : input_msg[i] * filter_msg[ARRAY_LENGTH-i-1];
      end
    end
  endgenerate
endmodule

`endif


