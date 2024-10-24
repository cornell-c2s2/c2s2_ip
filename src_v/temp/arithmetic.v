module cmn_Adder (
	in0,
	in1,
	cin,
	out,
	cout
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire cin;
	output wire [p_nbits - 1:0] out;
	output wire cout;
	assign {cout, out} = (in0 + in1) + {{p_nbits - 1 {1'b0}}, cin};
endmodule
module cmn_SimpleAdder (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire [p_nbits - 1:0] out;
	assign out = in0 + in1;
endmodule
module cmn_Subtractor (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire [p_nbits - 1:0] out;
	assign out = in0 - in1;
endmodule
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
module cmn_ZeroExtender (
	in,
	out
);
	parameter p_in_nbits = 1;
	parameter p_out_nbits = 8;
	input wire [p_in_nbits - 1:0] in;
	output wire [p_out_nbits - 1:0] out;
	assign out = {{p_out_nbits - p_in_nbits {1'b0}}, in};
endmodule
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
module cmn_ZeroComparator (
	in,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in;
	output wire out;
	assign out = in == {p_nbits {1'b0}};
endmodule
module cmn_EqComparator (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire out;
	assign out = in0 == in1;
endmodule
module cmn_LtComparator (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire out;
	assign out = in0 < in1;
endmodule
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
module cmn_RightLogicalShifter (
	in,
	shamt,
	out
);
	parameter p_nbits = 1;
	parameter p_shamt_nbits = 1;
	input wire [p_nbits - 1:0] in;
	input wire [p_shamt_nbits - 1:0] shamt;
	output wire [p_nbits - 1:0] out;
	assign out = in >> shamt;
endmodule
