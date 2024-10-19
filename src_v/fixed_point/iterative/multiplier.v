`default_nettype none
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
module cmn_Mux3 (
	in0,
	in1,
	in2,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [1:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			2'd0: out = in0;
			2'd1: out = in1;
			2'd2: out = in2;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux4 (
	in0,
	in1,
	in2,
	in3,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [1:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			2'd0: out = in0;
			2'd1: out = in1;
			2'd2: out = in2;
			2'd3: out = in3;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux5 (
	in0,
	in1,
	in2,
	in3,
	in4,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux6 (
	in0,
	in1,
	in2,
	in3,
	in4,
	in5,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [p_nbits - 1:0] in5;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			3'd5: out = in5;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux7 (
	in0,
	in1,
	in2,
	in3,
	in4,
	in5,
	in6,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [p_nbits - 1:0] in5;
	input wire [p_nbits - 1:0] in6;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			3'd5: out = in5;
			3'd6: out = in6;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux8 (
	in0,
	in1,
	in2,
	in3,
	in4,
	in5,
	in6,
	in7,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [p_nbits - 1:0] in5;
	input wire [p_nbits - 1:0] in6;
	input wire [p_nbits - 1:0] in7;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			3'd5: out = in5;
			3'd6: out = in6;
			3'd7: out = in7;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_MuxN (
	in,
	sel,
	out
);
	parameter nbits = 1;
	parameter ninputs = 2;
	input wire [(ninputs * nbits) - 1:0] in;
	input wire [$clog2(ninputs) - 1:0] sel;
	output wire [nbits - 1:0] out;
	assign out = in[((ninputs - 1) - sel) * nbits+:nbits];
endmodule
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
module fixed_point_iterative_Multiplier (
	clk,
	reset,
	recv_rdy,
	recv_val,
	a,
	b,
	send_rdy,
	send_val,
	c
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	parameter [0:0] sign = 1;
	input wire clk;
	input wire reset;
	output wire recv_rdy;
	input wire recv_val;
	input wire [n - 1:0] a;
	input wire [n - 1:0] b;
	input wire send_rdy;
	output wire send_val;
	output wire [n - 1:0] c;
	wire do_carry;
	wire do_add;
	wire in_wait;
	FXPIterMultControl #(
		.n(n),
		.d(d)
	) control(
		.clk(clk),
		.reset(reset),
		.recv_val(recv_val),
		.recv_rdy(recv_rdy),
		.send_val(send_val),
		.send_rdy(send_rdy),
		.in_wait(in_wait),
		.do_add(do_add),
		.do_carry(do_carry)
	);
	FXPIterMultDatapath #(
		.n(n),
		.d(d)
	) datapath(
		.clk(clk),
		.reset(reset),
		.in_wait(in_wait),
		.do_add(do_add),
		.do_carry((sign != 0) & do_carry),
		.a({{d {(sign != 0) & a[n - 1]}}, a}),
		.b(b),
		.c(c)
	);
endmodule
module FXPIterMultControl (
	clk,
	reset,
	recv_val,
	recv_rdy,
	send_val,
	send_rdy,
	in_wait,
	do_add,
	do_carry
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	input wire clk;
	input wire reset;
	input wire recv_val;
	output reg recv_rdy;
	output reg send_val;
	input wire send_rdy;
	output reg in_wait;
	output reg do_add;
	output reg do_carry;
	reg [1:0] IDLE = 2'd0;
	reg [1:0] CALC = 2'd1;
	reg [1:0] DONE = 2'd2;
	reg [1:0] state;
	reg [1:0] next_state;
	reg [$clog2(n) - 1:0] counter;
	reg counter_reset;
	function automatic signed [$clog2(n) - 1:0] sv2v_cast_2A747_signed;
		input reg signed [$clog2(n) - 1:0] inp;
		sv2v_cast_2A747_signed = inp;
	endfunction
	always @(*)
		case (state)
			IDLE:
				if (recv_val)
					next_state = CALC;
				else
					next_state = IDLE;
			CALC:
				if (counter == sv2v_cast_2A747_signed(n - 1))
					next_state = DONE;
				else
					next_state = CALC;
			DONE:
				if (send_rdy)
					next_state = IDLE;
				else
					next_state = DONE;
			default: next_state = IDLE;
		endcase
	always @(*)
		case (state)
			IDLE: begin
				in_wait = 1;
				do_add = 0;
				do_carry = 0;
				counter_reset = 0;
				recv_rdy = 1;
				send_val = 0;
			end
			CALC: begin
				in_wait = 0;
				do_add = 1;
				do_carry = counter == sv2v_cast_2A747_signed(n - 1);
				counter_reset = 0;
				recv_rdy = 0;
				send_val = 0;
			end
			DONE: begin
				in_wait = 0;
				do_add = 0;
				do_carry = 0;
				counter_reset = 1;
				recv_rdy = 0;
				send_val = 1;
			end
			default:
				;
		endcase
	always @(posedge clk)
		if (reset)
			state <= IDLE;
		else
			state <= next_state;
	always @(posedge clk)
		if (reset || counter_reset)
			counter <= 0;
		else if (state == CALC)
			counter <= counter + 1;
		else
			counter <= counter;
endmodule
module FXPIterMultDatapath (
	clk,
	reset,
	in_wait,
	do_add,
	do_carry,
	a,
	b,
	c
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	input wire clk;
	input wire reset;
	input wire in_wait;
	input wire do_add;
	input wire do_carry;
	input wire [(n + d) - 1:0] a;
	input wire [n - 1:0] b;
	output wire [n - 1:0] c;
	wire [(n + d) - 1:0] acc_in;
	wire [(n + d) - 1:0] acc_out;
	cmn_ResetReg #(.p_nbits(n + d)) acc_reg(
		.clk(clk),
		.reset(in_wait | reset),
		.d(acc_in),
		.q(acc_out)
	);
	wire [(n + d) - 1:0] a_const_out;
	cmn_EnResetReg #(.p_nbits(n + d)) a_const_reg(
		.clk(clk),
		.reset(reset),
		.en(in_wait),
		.d(a),
		.q(a_const_out)
	);
	wire [(n + d) - 1:0] a_in;
	wire [(n + d) - 1:0] a_out;
	cmn_ResetReg #(.p_nbits(n + d)) a_reg(
		.clk(clk),
		.reset(reset),
		.d(a_in),
		.q(a_out)
	);
	wire [n - 1:0] b_in;
	wire [n - 1:0] b_out;
	cmn_ResetReg #(.p_nbits(n)) b_reg(
		.clk(clk),
		.reset(reset),
		.d(b_in),
		.q(b_out)
	);
	cmn_Mux2 #(.p_nbits(n + d)) a_sel(
		.in0(a_out << 1),
		.in1(a),
		.sel(in_wait),
		.out(a_in)
	);
	cmn_Mux2 #(.p_nbits(n)) b_sel(
		.in0(b_out >> 1),
		.in1(b),
		.sel(in_wait),
		.out(b_in)
	);
	wire [(n + d) - 1:0] add_tmp;
	wire [(2 * n) - 1:0] carry_tmp;
	wire [(2 * n) - 1:0] carry_tmp2;
	assign carry_tmp = {{n - d {a_const_out[(n + d) - 1]}}, a_const_out};
	assign carry_tmp2 = ((carry_tmp << (d + 1)) - carry_tmp) << (n - 1);
	cmn_Mux2 #(.p_nbits(n + d)) carry_sel(
		.in0(a_out),
		.in1(carry_tmp2[(n + d) - 1:0]),
		.sel(do_carry),
		.out(add_tmp)
	);
	cmn_Mux2 #(.p_nbits(n + d)) add_sel(
		.in0(acc_out),
		.in1(acc_out + add_tmp),
		.sel(do_add & b_out[0]),
		.out(acc_in)
	);
	assign c = acc_out[(n + d) - 1:d];
endmodule
