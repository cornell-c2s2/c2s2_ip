module cmn_Incrementer (
	in,
	out
);
	parameter p_nbits = 1;
	parameter p_inc_value = 1;
	input wire [p_nbits - 1:0] in;
	output wire [p_nbits - 1:0] out;
	assign out = in + p_inc_value;
endmodule
