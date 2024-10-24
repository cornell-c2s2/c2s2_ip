module cmn_GtComparator (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire out;
	assign out = in0 > in1;
endmodule
