//================================================
// template.v
//================================================

`ifndef TEMPLATE_V
`define TEMPLATE_V

module Template 
# (
  parameter width = 32,
) (
  input  logic clk,
  input  logic reset,

	output logic recv_rdy,
	input  logic recv_val,
  input  logic [width-1:0] recv_msg,

	input  logic send_rdy,
	output logic send_val,
  output logic [width-1:0] send_msg,
);

endmodule

`endif /* TEMPLATE_V */