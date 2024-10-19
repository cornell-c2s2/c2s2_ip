module cmn_Reg (
	clk,
	q,
	d
);
	parameter p_nbits = 1;
	input wire clk;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	always @(posedge clk) q <= d;
endmodule
module cmn_ResetReg (
	clk,
	reset,
	q,
	d
);
	parameter p_nbits = 1;
	parameter p_reset_value = 0;
	input wire clk;
	input wire reset;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	always @(posedge clk) q <= (reset ? p_reset_value : d);
endmodule
module cmn_EnReg (
	clk,
	q,
	d,
	en
);
	parameter p_nbits = 1;
	input wire clk;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	input wire en;
	always @(posedge clk)
		if (en)
			q <= d;
endmodule
module cmn_EnResetReg (
	clk,
	reset,
	q,
	d,
	en
);
	parameter p_nbits = 1;
	parameter p_reset_value = 0;
	input wire clk;
	input wire reset;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	input wire en;
	function automatic signed [p_nbits - 1:0] sv2v_cast_BBED6_signed;
		input reg signed [p_nbits - 1:0] inp;
		sv2v_cast_BBED6_signed = inp;
	endfunction
	always @(posedge clk)
		if (reset || en)
			q <= (reset ? sv2v_cast_BBED6_signed(p_reset_value) : d);
endmodule
module cmn_BasicCounter (
	clk,
	reset,
	clear,
	increment,
	decrement,
	count,
	count_is_zero,
	count_is_max
);
	parameter p_count_nbits = 3;
	parameter p_count_clear_value = 0;
	parameter p_count_max_value = 4;
	input wire clk;
	input wire reset;
	input wire clear;
	input wire increment;
	input wire decrement;
	output wire [p_count_nbits - 1:0] count;
	output wire count_is_zero;
	output wire count_is_max;
	wire [p_count_nbits - 1:0] count_next;
	cmn_ResetReg #(
		.p_nbits(p_count_nbits),
		.p_reset_value(p_count_clear_value)
	) count_reg(
		.clk(clk),
		.reset(reset),
		.d(count_next),
		.q(count)
	);
	wire do_increment;
	assign do_increment = increment && (count < p_count_max_value);
	wire do_decrement;
	assign do_decrement = decrement && (count > 0);
	assign count_next = (clear ? p_count_clear_value : (do_increment ? count + 1 : (do_decrement ? count - 1 : count)));
	assign count_is_zero = count == 0;
	assign count_is_max = count == p_count_max_value;
endmodule
