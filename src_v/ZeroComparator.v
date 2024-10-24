module cmn_ZeroComparator (
	in,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in;
	output wire out;
	assign out = in == {p_nbits {1'b0}};
endmodule
