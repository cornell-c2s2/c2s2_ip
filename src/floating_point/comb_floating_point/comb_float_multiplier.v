//================================================
// comb_float_multiplier.v
// 
// Combinational floating point multiplier
// Author: Mattie Lee (mll264)
// Additional credits: Barry Lyu (fl327), Xilai Dai (xd44)
//================================================

`ifndef COMB_FLOAT_MULTIPLIER_V
`define COMB_FLOAT_MULTIPLIER_V

`include "src/cmn/muxes.v"
`include "src/fixed_point/combinational/multiplier.v"

module CombFloatMultiplier #(
  parameter int BIT_WIDTH = 32,
  parameter int M_WIDTH = 23,
  parameter int E_WIDTH = 8

) (
  input  logic [BIT_WIDTH - 1:0] in0,
  input  logic [BIT_WIDTH - 1:0] in1,
  output logic [BIT_WIDTH - 1:0] out
);

  logic s0, s1, sout;  //sign
  logic [E_WIDTH - 1:0]   e0, e1, eout;  // exponent
  logic [M_WIDTH - 1:0]   m0, m1, mout;  // mantissa
  logic [BIT_WIDTH - 1:0] normal_out, special_out;
  logic use_special;

  // bias is 2^(e_width - 1) - 1
  logic [E_WIDTH - 1:0] bias = '1 >> 1;

  assign s0 = in0[BIT_WIDTH - 1];
  assign e0 = in0[BIT_WIDTH - 2:M_WIDTH];
  assign m0 = in0[M_WIDTH - 1:0];

  assign s1 = in1[BIT_WIDTH - 1];
  assign e1 = in1[BIT_WIDTH - 2:M_WIDTH];
  assign m1 = in1[M_WIDTH - 1:0];


  // mantissa
  // product of the mantissas must be 2 bits longer than
  // mantissa so that we can effectively normalize it afterwards.
  logic [M_WIDTH + 1:0] mout_long;
  FixedPointCombMultiplier #(
    .n   (M_WIDTH + 2),
    .d   (M_WIDTH - 1), // TODO: This might be wrong!
    .sign(0)
  ) mantissa_mult (
    .a({1'b1, m0}),   // add the hidden bit
    .b({1'b1, m1}),
    .c(mout_long)
  );

  // normalize the mantissa
  // this is equivalent to a right shift if the
  // MSB is 1. We can discard the MSB since it
  // will become the hidden bit anyway.
  cmn_Mux2 #(
    .p_nbits(M_WIDTH)
  ) mantissa_mux (
    .in0(mout_long[M_WIDTH - 1:0]), // no shift
    .in1(mout_long[M_WIDTH:1]), // right shifted
    .sel(mout_long[M_WIDTH + 1]), // MSB
    .out(mout)
  );

  // exponent
  // add the MSB of mantissa product as part of normalization
  // if the MSB is 1 then we are right shifting the mantissa
  // so we need to increment the exponent as well.
  assign eout = e0 + e1 - bias + mout_long[M_WIDTH + 1];

  // sign
  assign sout = s0 ^ s1;

  assign normal_out = {sout, eout, mout};

  // Special cases
  // AUTHOR CREDITS: this code is from Barry and Xilai's multiplier
  always_comb begin
    // defaults
    use_special = 0;
    special_out = 0;

    if ((e0 == 255) && (m1 != 0)) begin
      // if in0 is NaN, keep all bits
      use_special = 1'b1;
      special_out = in0;

    end else if ((e1 == 255) && (m1 != 0)) begin
      // if in1 is NaN, keep all bits
      use_special = 1'b1;
      special_out = in1;

    end else if ((e0 == 255) && (in1[30:0] != 0)) begin
      // in0 is infinity, in1 is not zero
      use_special = 1'b1;
      special_out = {sout, 8'd255, 23'd0};

    end else if ((e1 == 255) && (in0[30:0] != 0)) begin
      // in1 is infinity, in0 is not zero
      use_special = 1;
      special_out = {sout, 8'd255, 23'd0};

    end else if ((e0 == 255) || (e1 == 255)) begin
      // one is infinity, the other is zero, return NaN
      use_special = 1;
      special_out = 32'hFFC00000;
    end
  end

  // choose between normal output and special output
  cmn_Mux2 #(
    .p_nbits(32)
  ) output_mux (
    .in0(normal_out),
    .in1(special_out),
    .sel(use_special),
    .out(out)
  );

endmodule


`endif
