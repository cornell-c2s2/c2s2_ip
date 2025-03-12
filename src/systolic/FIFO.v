`ifndef FIFO_V
`define FIFO_V

module FIFO
#(
  parameter size  = 3
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

  logic [$clog(size)-1:0] wptr;
  logic [$clog(size)-1:0] rptr;

  logic [$clog(size)-1:0] wptr_next;
  logic [$clog(size)-1:0] rptr_next;

  logic [nbits-1:0] q [size];

  // Write-Only Logic

  assign wptr_next = ((wptr + 1) == (size - 1) ? 0 : wptr + 1);

  always_ff @(posedge clk) begin
    if(rst)
      wptr <= 0;
    else if(wen & ~ren & ~_full) begin
      q[wptr] <= d_in;
      wptr    <= wptr_next;
    end
  end

  // Read-Only Logic

  assign rptr_next = ((rptr + 1) == (size - 1) ? 0 : wptr + 1);

  always_ff @(posedge clk) begin
    if(rst)
      rptr <= 0;
    else if(~wen & ren & ~_empty) begin
      q_out <= q[rptr];
      rptr  <= r_ptr + 1;
    end
    else
      q_out <= 0;
  end

  // Status Signals

  always_ff @(posedge clk) begin
    if(rst) begin
      _full  <= 0;
      _empty <= 1;
    end
    else begin
      _full  <= (wen & ~ren) & (wptr_next == rptr);
      _empty <= (~wen & ren) & (wptr == rptr_next);
    end
  end

  assign full  = _full;
  assign empty = _empty;

endmodule

`endif