module cmn_SignExtender (
	in,
	out
);
	parameter p_in_nbits = 1;
	parameter p_out_nbits = 8;
	input wire [p_in_nbits - 1:0] in;
	output wire [p_out_nbits - 1:0] out;
	assign out = {{p_out_nbits - p_in_nbits {in[p_in_nbits - 1]}}, in};
endmodule
