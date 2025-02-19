//==============================================================================
// Systolic Matrix Multiplier Processing Element
//==============================================================================

`include "cmn/regs.v"
`include "fixed_point/combinational/multiplier.v"

`ifndef SYSTOLICMMPE_V
`define SYSTOLICMMPE_V

module SystolicMMPE
#(
  parameter int n = 16,
  parameter int d = 8,
  parameter bit sign = 1
)(
  input  logic         clk,
  input  logic         rst,
  input  logic         en,

  input  logic [n-1:0] x_in,
  input  logic [n-1:0] w_in,

  output logic [n-1:0] x_out,
  output logic [n-1:0] w_out,
  output logic [n-1:0] s_out
);

  // Multiplication

  logic [n-1:0]    prod;
  logic [n+d-1:0] _prod;
  logic [d-1:0]   _prod_unused;

  /*fixed_point_combinational_Multiplier #(n, d, sign) multiplier
  (
    .a (x_in),
    .b (w_in),
    .c (prod)
  );*/

  always_comb begin
    _prod = (x_in * w_in);
    prod  = _prod[n+d-1:d];
  end

  assign _prod_unused = _prod[d-1:0];

  // Summation

  logic [n-1:0] sum;
  logic [n-1:0] sum_next;

  always_comb begin
    sum_next = sum + prod;
  end

  cmn_EnResetReg #(n, 0) sum_reg
  (
    .clk   (clk),
    .reset (rst),
    .en    (en),
    .d     (sum_next),
    .q     (sum)
  );

  assign s_out = sum;

  // Tensor & Weight Propagation

  cmn_EnResetReg #(n, 0) x_reg
  (
    .clk   (clk),
    .reset (rst),
    .en    (en),
    .d     (x_in),
    .q     (x_out)
  );

  cmn_EnResetReg #(n, 0) w_reg
  (
    .clk   (clk),
    .reset (rst),
    .en    (en),
    .d     (w_in),
    .q     (w_out)
  );

endmodule

`endif /* SYSTOLICMMPE_V */