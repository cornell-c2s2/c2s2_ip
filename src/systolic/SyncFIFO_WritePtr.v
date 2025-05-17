`ifndef SYNCFIFO_WRITEPTR_V
`define SYNCFIFO_WRITEPTR_V

module SyncFIFO_WritePtr
#(
  parameter DEPTH     = 4,
  parameter PTR_WIDTH = $clog2(DEPTH) + 1
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 wen,
  input  logic [PTR_WIDTH-1:0] r_ptr,
  output logic [PTR_WIDTH-1:0] w_ptr,
  output logic                 full
);

  logic                 _full;
  logic [PTR_WIDTH-1:0] _w_ptr;
  logic [PTR_WIDTH-1:0] _w_ptr_next;

  assign _w_ptr_next = _w_ptr + {{(PTR_WIDTH-1){1'b0}}, (wen & ~_full)};

  always_ff @(posedge clk) begin
    _w_ptr <= (rst ? 0 : _w_ptr_next);
  end

  assign _full = (_w_ptr[PTR_WIDTH-1] == ~r_ptr[PTR_WIDTH-1]) 
               & (_w_ptr[PTR_WIDTH-2:0] == r_ptr[PTR_WIDTH-2:0]);
  
  assign w_ptr = _w_ptr;
  assign full  = _full;

endmodule

`endif