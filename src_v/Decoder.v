module Decoder (
	in,
	out
);
	parameter signed [31:0] BIT_WIDTH = 3;
	input wire [BIT_WIDTH - 1:0] in;
	output wire [(1 << BIT_WIDTH) - 1:0] out;
	assign out = {{(1 << BIT_WIDTH) - 1 {1'b0}}, 1'b1} << in;
endmodule
