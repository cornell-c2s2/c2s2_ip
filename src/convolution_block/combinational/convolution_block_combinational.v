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
  // input array
  input  logic [BIT_WIDTH - 1:0] req1_msg[ARRAY_LENGTH - 1:0],

  // input filter (array that gets reversed)
  input  logic [BIT_WIDTH - 1:0] req2_msg[ARRAY_LENGTH - 1:0],

  // output array
  output logic [BIT_WIDTH - 1:0] resp_msg[ARRAY_LENGTH - 1:0]
);

  // perform array convolution: output[i] = input[i] * filter[n - i]
  generate
    for (genvar i = 0; i < ARRAY_LENGTH; i++) begin
        assign resp_msg[i] = req1_msg[i] * req2_msg[ARRAY_LENGTH-i-1];
    end
  endgenerate
endmodule

`endif


