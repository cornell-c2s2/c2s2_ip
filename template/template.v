//================================================
// template.v
//================================================

`ifndef TEMPLATE_V
`define TEMPLATE_V

module template
(
  input  logic clk;
  input  logic q;
  output logic d;
);

always_ff @( posedge clk )
  q <= d;

endmodule

`endif