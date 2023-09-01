//================================================
// template.v
//================================================

module template
(
  input  logic clk;
  input  logic q;
  output logic d;
);

always_ff @( posedge clk )
  q <= d;

endmodule
