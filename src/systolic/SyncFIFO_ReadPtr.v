`ifndef SYNCFIFO_READPTR_V
`define SYNCFIFO_READPTR_V

module SyncFIFO_ReadPtr
#(
  parameter DEPTH     = 4,
  parameter PTR_WIDTH = $clog2(DEPTH) + 1
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 ren,
  input  logic [PTR_WIDTH-1:0] w_ptr,
  output logic [PTR_WIDTH-1:0] r_ptr,
  output logic                 empty
);

  logic                 _empty;
  logic [PTR_WIDTH-1:0] _r_ptr;
  logic [PTR_WIDTH-1:0] _r_ptr_next;

  assign _r_ptr_next = _r_ptr + {{(PTR_WIDTH-1){1'b0}}, (ren & ~_empty)};

  always_ff @(posedge clk) begin
    _r_ptr <= (rst ? 0 : _r_ptr_next);
  end

  assign _empty = (w_ptr == _r_ptr);

  assign r_ptr = _r_ptr;
  assign empty = _empty;

endmodule

`endif