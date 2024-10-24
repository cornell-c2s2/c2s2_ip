module cmn_Mux2 (
	in0,
	in1,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			1'd0: out = in0;
			1'd1: out = in1;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
