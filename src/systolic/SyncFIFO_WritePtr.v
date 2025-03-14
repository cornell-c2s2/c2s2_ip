`ifndef SYNCFIFO_WRITEPTR_V
`define SYNCFIFO_WRITEPTR_V

module SyncFIFO_WritePtr
#(
  parameter depth     = 16,
  parameter ptr_width = $clog2(depth) + 1
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 wen,
  input  logic [ptr_width-1:0] r_ptr,
  output logic [ptr_width-1:0] w_ptr,
  output logic                 full
);

  logic                 _full;
  logic [ptr_width-1:0] _w_ptr;
  logic [ptr_width-1:0] _w_ptr_next;

  assign _w_ptr_next = _w_ptr + (wen & ~_full);

  always_ff @(posedge clk) begin
    _w_ptr <= (rst ? 0 : _w_ptr_next);
  end

  assign _full = (_w_ptr[ptr_width-1] == ~r_ptr[ptr_width-1]) 
               & (_w_ptr[ptr_width-2:0] == r_ptr[ptr_width-2:0]);
  
  assign w_ptr = _w_ptr;
  assign full  = _full;

endmodule

`endif