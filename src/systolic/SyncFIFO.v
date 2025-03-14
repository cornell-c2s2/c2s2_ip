`ifndef SYNCFIFO_V
`define SYNCFIFO_V

`include "systolic/SyncFIFO_ReadPtr.v"
`include "systolic/SyncFIFO_WritePtr.v"

module SyncFIFO
#(
  parameter depth     = 16,
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

  logic _full;
  logic _empty;

  logic [ptr_width-1:0] r_ptr;
  logic [ptr_width-1:0] w_ptr;

  logic [nbits-1:0] mem [depth];

  // Synchronous R/W Pointers

  SyncFIFO_ReadPtr #(depth) r_ptr_blk
  (
    .clk   (clk),
    .rst   (rst),
    .ren   (ren),
    .w_ptr (w_ptr),
    .r_ptr (r_ptr),
    .empty (_empty)
  );

  SyncFIFO_WritePtr #(depth) w_ptr_blk
  (
    .clk   (clk),
    .rst   (rst),
    .wen   (wen),
    .r_ptr (r_ptr),
    .w_ptr (w_ptr),
    .full  (_full)
  );

  assign full  = _full;
  assign empty = _empty;

  // Synchronous R/W Logic

  always_ff @(posedge clk) begin
    if(wen & ~_full)
      mem[w_ptr[ptr_width-2:0]] <= d;
  end

  assign q = ((ren & ~_empty) ? mem[r_ptr[ptr_width-2:0]] : 0);

endmodule

`endif