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
  input  logic [31:0] in0,
  input  logic [31:0] in1,
  output logic [31:0] out
);

  logic s0, s1, sout;  //sign
  logic [7:0] e0, e1, eout;  // exponent
  logic [22:0] m0, m1, mout;  // mantissa

  logic [7:0] bias = 8'd127;  // bias for 32 bit floating pt

  assign s0   = in0[31];
  assign e0   = in0[30:23];
  assign m0   = in0[22:0];

  assign s1   = in1[31];
  assign e1   = in1[30:23];
  assign m1   = in1[22:0];

  // sign 
  assign sout = s0 ^ s1;

  // exponent 
  assign eout = e0 + e1 - bias;

  // mantissa
  FixedPointCombMultiplier #(
    .n   (24),
    .d   (23),
    .sign(0)
  ) mantissa_mult (
    .a({1, m0}),
    .b({1, m1}),
    .c({1, mout})
  );

endmodule


`endif
