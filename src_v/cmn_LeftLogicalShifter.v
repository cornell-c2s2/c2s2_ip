module cmn_LeftLogicalShifter (
	in,
	shamt,
	out
);
	parameter p_nbits = 1;
	parameter p_shamt_nbits = 1;
	input wire [p_nbits - 1:0] in;
	input wire [p_shamt_nbits - 1:0] shamt;
	output wire [p_nbits - 1:0] out;
	assign out = in << shamt;
endmodule
