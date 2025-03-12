`ifndef SYSTOLICBUFFER_V
`define SYSTOLICBUFFER_V

module SystolicBuffer
#(
  parameter depth     = 3,
  parameter nbits     = 16,
  parameter ptr_width = $clog2(depth)
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

  logic write_only;
  logic read_only;
  
  logic [ptr_width-1:0] w_ptr;
  logic [ptr_width-1:0] r_ptr;

  logic [ptr_width-1:0] w_ptr_next;
  logic [ptr_width-1:0] r_ptr_next;

  logic [nbits-1:0] mem [depth];

  // R/W Pointers

  assign write_only = (wen & ~ren & ~_full);
  assign read_only  = (ren & ~wen & ~_empty);

  assign w_ptr_next = w_ptr + {{(ptr_width-1){1'b0}}, write_only};
  assign r_ptr_next = r_ptr + {{(ptr_width-1){1'b0}}, read_only};

  always_ff @(posedge clk) begin
    if(rst) begin
      w_ptr <= 0;
      r_ptr <= 0;
    end else begin
      w_ptr <= w_ptr_next;
      r_ptr <= r_ptr_next;
    end
  end

  // Write Logic

  always_ff @(posedge clk) begin
    if(rst) begin
      for(int i = 0; i < depth; i++)
        mem[i] <= 0;
    end else begin
      mem[w_ptr] <= (write_only ? d : mem[w_ptr]);
    end
  end

  // Read Logic

  assign q = (read_only ? mem[r_ptr] : 0);

  // Status Signals

  assign _full  = (w_ptr == depth);
  assign _empty = (r_ptr == depth);

  assign full  = _full;
  assign empty = _empty;

endmodule

`endif