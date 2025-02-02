//==============================================================================
// Matrix Multiplier Processing Element
//==============================================================================

`include "cmn/regs.v"
`include "fixed_point/combinational/multiplier.v"

`ifndef MATRIXMULTIPLIER_PE_V
`define MATRIXMULTIPLIER_PE_V

module MatrixMultiplier_PE
#(
  parameter nbits=16
)(
  (* keep=1 *) input  logic             clk,
  (* keep=1 *) input  logic             rst,
  (* keep=1 *) input  logic             en,

  (* keep=1 *) input  logic [nbits-1:0] x_in,
  (* keep=1 *) input  logic [nbits-1:0] w_in,

  (* keep=1 *) output logic [nbits-1:0] x_out,
  (* keep=1 *) output logic [nbits-1:0] w_out,
  (* keep=1 *) output logic [nbits-1:0] s_out
);



endmodule

`endif /* MATRIXMULTIPLIER_PE_V */