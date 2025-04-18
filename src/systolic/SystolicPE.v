`include "cmn/regs.v"
`include "fixed_point/combinational/multiplier.v"

`ifndef SYSTOLICPE_V
`define SYSTOLICPE_V

module SystolicPE
#(
  parameter NBITS = 16,
  parameter DBITS = 8,
  parameter SIGN = 1
)(
  input  logic         clk,
  input  logic         rst,
  input  logic         en,

  input  logic [NBITS-1:0] x_in,
  input  logic [NBITS-1:0] w_in,

  output logic [NBITS-1:0] x_out,
  output logic [NBITS-1:0] w_out,
  output logic [NBITS-1:0] s_out
);

  // Multiplication

  logic [NBITS-1:0] prod;

  fixed_point_combinational_Multiplier #(NBITS, DBITS, SIGN) multiplier
  (
    .a (x_in),
    .b (w_in),
    .c (prod)
  );

  // Summation

  logic [NBITS-1:0] sum;
  logic [NBITS-1:0] sum_next;

  always_comb begin
    sum_next = sum + prod;
  end

  cmn_EnResetReg #(NBITS, 0) sum_reg
  (
    .clk   (clk),
    .reset (rst),
    .en    (en),
    .d     (sum_next),
    .q     (sum)
  );

  assign s_out = sum;

  // Tensor & Weight Propagation

  cmn_EnResetReg #(NBITS, 0) x_reg
  (
    .clk   (clk),
    .reset (rst),
    .en    (en),
    .d     (x_in),
    .q     (x_out)
  );

  cmn_EnResetReg #(NBITS, 0) w_reg
  (
    .clk   (clk),
    .reset (rst),
    .en    (en),
    .d     (w_in),
    .q     (w_out)
  );

endmodule

`endif /* SYSTOLICPE_V */