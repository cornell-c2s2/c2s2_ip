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
  (* keep=1 *) input  logic         clk,
  (* keep=1 *) input  logic         rst,
  (* keep=1 *) input  logic         en,

  (* keep=1 *) input  logic [n-1:0] x_in,
  (* keep=1 *) input  logic [n-1:0] w_in,

  (* keep=1 *) output logic [n-1:0] x_out,
  (* keep=1 *) output logic [n-1:0] w_out,
  (* keep=1 *) output logic [n-1:0] s_out
);

  // Multiplication

  logic [n-1:0] prod;

  fixed_point_combinational_Multiplier #(n, d, sign) multiplier
  (
    .a (x_in),
    .b (w_in),
    .c (prod)
  );

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