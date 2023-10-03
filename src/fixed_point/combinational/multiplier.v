`default_nettype none
`ifndef FIXED_POINT_COMB_MULTIPLIER
`define FIXED_POINT_COMB_MULTIPLIER

module FixedPointCombMultiplier #(
  parameter int n = 32,  // bit width
  parameter int d = 16,  // number of decimal bits
  parameter bit sign = 1  // 1 if signed, 0 otherwise.
) (
  input  logic [n-1:0] a,
  input  logic [n-1:0] b,
  output logic [n-1:0] c
);

  logic [2*n-1:0] prod;
  logic [2*n-1:0] a_ext, b_ext;

  generate
    if (sign) begin
      assign a_ext = {{n{a[n-1]}}, a};
      assign b_ext = {{n{b[n-1]}}, b};
      assign prod  = (a_ext * b_ext) >>> d;
    end else begin
      assign prod = (a * b) >> d;
    end
  endgenerate

  assign c = prod[n-1:0];

endmodule

`endif
