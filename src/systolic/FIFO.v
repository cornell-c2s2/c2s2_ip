`ifndef FIFO_V
`define FIFO_V

module FIFO
#(
  parameter size  = 3,
  parameter nbits = 16
)(
  input  logic             clk,
  input  logic             rst,
  input  logic             wen,
  input  logic             ren,
  input  logic [nbits-1:0] d_in,
  output logic             full,
  output logic             empty,
  output logic [nbits-1:0] q_out
);

  logic _full;
  logic _empty;

  logic [$clog2(size)-1:0] wptr;
  logic [$clog2(size)-1:0] rptr;

  logic [$clog2(size)-1:0] wptr_next;
  logic [$clog2(size)-1:0] rptr_next;

  logic [nbits-1:0] q [size];

  // Write-Only Logic

  assign wptr_next = ((wptr + 1) == size ? 0 : wptr + 1);

  always_ff @(posedge clk) begin
    if(rst) begin
      wptr  <= 0;
      _full <= 0;
    end
    else if(wen & ~ren & ~_full) begin
      q[wptr] <= d_in;
      wptr    <= wptr_next;
      _full   <= (wptr_next == rptr);
    end
    else begin
      q[wptr] <= q[wptr];
      wptr  <= wptr;
      _full <= _full;
    end
  end

  assign full = _full;

  // Read-Only Logic

  assign rptr_next = ((rptr + 1) == size ? 0 : rptr + 1);

  always_ff @(posedge clk) begin
    if(rst) begin
      rptr   <= 0;
      _empty <= 1;
    end
    else if(~wen & ren & ~_empty) begin
      q_out  <= q[rptr];
      rptr   <= rptr_next;
      _empty <= (wptr == rptr_next);
    end
    else begin
      q_out  <= 0;
      rptr   <= rptr;
      _empty <= _empty;
    end
  end

  assign empty = _empty;

endmodule

`endif