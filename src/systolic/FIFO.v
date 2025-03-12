`ifndef FIFO_V
`define FIFO_V

module FIFO
#(
  parameter depth     = 3,
  parameter nbits     = 16,
  parameter ptr_width = $clog2(depth)
)(
  input  logic             clk,
  input  logic             rst,
  input  logic             wen,
  input  logic             ren,
  //input  logic [nbits-1:0] d_in,
  output logic             full,
  output logic             empty,
  //output logic [nbits-1:0] q_out
);

  logic _full;
  logic _empty;

  logic [ptr_width-1:0] wptr;
  logic [ptr_width-1:0] rptr;

  logic [ptr_width-1:0] wptr_next;
  logic [ptr_width-1:0] rptr_next;

  //logic [nbits-1:0] q [depth];

  // R/W Pointers

  assign wptr_next = wptr + (wen & ~_full);
  assign rptr_next = rptr + (ren & ~_empty);

  always_ff @(posedge clk) begin
    if(rst) begin
      wptr <= 0;
      rptr <= 0;
    end else begin
      wptr <= (wptr_next == depth ? 0 : wptr_next);
      rptr <= (rptr_next == depth ? 0 : rptr_next);
    end
  end

  // Status Signals

  assign _full  = (wptr_next > rptr);
  assign _empty = (wptr == rptr);

  assign full  = _full;
  assign empty = _empty;
  
endmodule

`endif