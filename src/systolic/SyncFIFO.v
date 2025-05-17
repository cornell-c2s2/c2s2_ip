`ifndef SYNCFIFO_V
`define SYNCFIFO_V

`include "systolic/SyncFIFO_ReadPtr.v"
`include "systolic/SyncFIFO_WritePtr.v"

module SyncFIFO
#(
  parameter DEPTH     = 4,
  parameter NBITS     = 16,
  parameter PTR_WIDTH = $clog2(DEPTH) + 1
)(
  input  logic             clk,
  input  logic             rst,
  input  logic             wen,
  input  logic             ren,
  input  logic [NBITS-1:0] d,
  output logic [NBITS-1:0] q,
  output logic             full,
  output logic             empty
);

  logic _full;
  logic _empty;

  logic [PTR_WIDTH-1:0] r_ptr;
  logic [PTR_WIDTH-1:0] w_ptr;

  logic [NBITS-1:0] mem [DEPTH];

  // Synchronous R/W Pointers

  SyncFIFO_ReadPtr #(DEPTH) r_ptr_blk
  (
    .clk   (clk),
    .rst   (rst),
    .ren   (ren),
    .w_ptr (w_ptr),
    .r_ptr (r_ptr),
    .empty (_empty)
  );

  SyncFIFO_WritePtr #(DEPTH) w_ptr_blk
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
      mem[w_ptr[PTR_WIDTH-2:0]] <= d;
  end

  assign q = ((ren & ~_empty) ? mem[r_ptr[PTR_WIDTH-2:0]] : 0);

endmodule

`endif