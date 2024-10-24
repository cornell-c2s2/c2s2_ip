module regs_shift_Bitwise (
	clk,
	reset,
	d,
	en,
	load,
	load_en,
	q
);
	parameter signed [31:0] p_nbits = 8;
	parameter [0:0] p_reset_value = 0;
	input wire clk;
	input wire reset;
	input wire d;
	input wire en;
	input wire [p_nbits - 1:0] load;
	input wire load_en;
	output reg [p_nbits - 1:0] q;
	always @(posedge clk)
		if (reset)
			q <= {p_nbits {p_reset_value}};
		else if (load_en)
			q <= load;
		else if (~load_en & en)
			q <= {q[p_nbits - 2:0], d};
		else
			q <= q;
endmodule
