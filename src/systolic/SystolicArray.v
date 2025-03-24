`include "serdes/deseriaizer.v"
`include "systolic/SystolicDpath.v"

`ifndef SYSTOLICARRAY_V
`define SYSTOLICARRAY_V

module SystolicArray
#(
  parameter size  = 16,
  parameter nbits = 16,
  parameter dbits = 8
)(
  input logic             clk,
  input logic             rst,
  input logic [nbits-1:0] x_col_in,
  input logic [nbits-1:0] w_row_in
);

  

endmodule

`endif