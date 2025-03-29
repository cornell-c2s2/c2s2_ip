`include "serdes/deserializer.v"
`include "systolic/SystolicDpath.v"

`ifndef SYSTOLICARRAY_V
`define SYSTOLICARRAY_V

module SystolicArray
#(
  parameter size  = 16,
  parameter nbits = 16,
  parameter dbits = 8
)(
  input  logic                    clk,
  input  logic                    rst,

);



endmodule

`endif