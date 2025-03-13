`ifndef SYSTOLICFIFO_V
`define SYSTOLICFIFO_V

module SystolicFIFO
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

  logic _full;
  logic _empty;

  logic [ptr_width-1:0] w_ptr;
  logic [ptr_width-1:0] r_ptr;

  logic [ptr_width-1:0] w_ptr_next;
  logic [ptr_width-1:0] r_ptr_next;

  // R/W Pointers

  assign w_ptr_next = w_ptr + (wen & ~_full);
  assign r_ptr_next = r_ptr + (ren & ~_empty);

  always_ff @(posedge clk) begin
    if(rst) begin
      w_ptr <= 0;
      r_ptr <= 0;
    end else begin
      w_ptr <= w_ptr_next;
      r_ptr <= r_ptr_next;
    end
  end

  assign _full  = ((w_ptr - r_ptr) == depth);
  assign _empty = (w_ptr == r_ptr);

  // Write Logic

  //

  // Read Logic

  //

  // Status Signals

  assign full  = _full;
  assign empty = _empty;

endmodule

`endif