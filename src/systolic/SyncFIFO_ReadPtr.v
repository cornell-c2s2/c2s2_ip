`ifndef SYNCFIFO_READPTR_V
`define SYNCFIFO_READPTR_V

module SyncFIFO_ReadPtr
#(
  parameter depth     = 4,
  parameter ptr_width = $clog2(depth) + 1
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 ren,
  input  logic [ptr_width-1:0] w_ptr,
  output logic [ptr_width-1:0] r_ptr,
  output logic                 empty
);

  logic                 _empty;
  logic [ptr_width-1:0] _r_ptr;
  logic [ptr_width-1:0] _r_ptr_next;

  assign _r_ptr_next = _r_ptr + {{(ptr_width-1){1'b0}}, (ren & ~_empty)};

  always_ff @(posedge clk) begin
    _r_ptr <= (rst ? 0 : _r_ptr_next);
  end

  assign _empty = (w_ptr == _r_ptr);

  assign r_ptr = _r_ptr;
  assign empty = _empty;

endmodule

`endif