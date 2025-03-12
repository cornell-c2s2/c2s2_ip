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

  logic [nbits-1:0] q [size];

  // R/W Pointers

  logic _full;
  logic _empty;

  logic [$clog2(size)-1:0] w_ptr;
  logic [$clog2(size)-1:0] r_ptr;

  assign _full  = ((w_ptr + 1) == r_ptr);
  assign _empty = (w_ptr == r_ptr);

  // Write logic

  always_ff @(posedge clk) begin
    if(rst)
      w_ptr <= 0;
    else if(wen & !_full) begin
      q[w_ptr] <= d_in;
      w_ptr    <= w_ptr + 1;
    end
  end

  // Read Logic

  always_ff @(posedge clk) begin
    if(rst)
      r_ptr <= 0;
    else if(ren & !_empty) begin
      q_out <= q[r_ptr];
      r_ptr <= r_ptr + 1;
    end
    else
      q_out <= 0;
  end

  // Status Signals

  assign full  = _full;
  assign empty = _empty;

endmodule

`endif