//================================================
// comb_float_multiplier.v
// 
// Combinational floating point multiplier
// Author: Mattie Lee (mll264)
//================================================

`ifndef COMB_FLOAT_MULTIPLIER_V
`define COMB_FLOAT_MULTIPLIER_V

module comb_float_multiplier #(
) (
  input  logic [15:0] in0,
  input  logic [15:0] in1,
  output logic [15:0] out
);

  logic s0, s1;
  logic [3:0] e0, e1;
  logic [10:0] m0, m1;


endmodule


`endif
