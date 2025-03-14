`ifndef SYNCFIFO_V
`define SYNCFIFO_V

`include "systolic/SyncFIFO_ReadPtr.v"
`include "systolic/SyncFIFO_WritePtr.v"

module SyncFIFO
#(
  parameter depth     = 4,
  parameter nbits     = 16,
  parameter ptr_width = $clog2(depth) + 1
)(
  input  logic             clk,
  input  logic             rst,
  input  logic             wen,
  input  logic             ren,
  input  logic [nbits-1:0] d,
  output logic [nbits-1:0] q,
  output logic             full,
  output logic             empty
);

  logic [ptr_width-1:0] r_ptr;
  logic [ptr_width-1:0] w_ptr;

  SyncFIFO_ReadPtr #(depth) r_ptr_blk
  (
    .*
  );

  SyncFIFO_WritePtr #(depth) w_ptr_blk
  (
    .*
  );

endmodule

`endif