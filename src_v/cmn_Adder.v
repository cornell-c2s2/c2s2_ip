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
