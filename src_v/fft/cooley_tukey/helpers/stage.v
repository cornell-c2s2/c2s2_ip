module fft_cooley_tukey_helpers_TwiddleGenerator (
	sine_wave_in,
	twiddle_real,
	twiddle_imaginary
);
	parameter signed [31:0] BIT_WIDTH = 4;
	parameter signed [31:0] DECIMAL_PT = 2;
	parameter signed [31:0] SIZE_FFT = 8;
	parameter signed [31:0] STAGE_FFT = 0;
	input wire [(SIZE_FFT * BIT_WIDTH) - 1:0] sine_wave_in;
	output wire [((SIZE_FFT / 2) * BIT_WIDTH) - 1:0] twiddle_real;
	output wire [((SIZE_FFT / 2) * BIT_WIDTH) - 1:0] twiddle_imaginary;
	genvar m;
	generate
		for (m = 0; m < (2 ** STAGE_FFT); m = m + 1) begin : genblk1
			genvar i;
			for (i = 0; i < SIZE_FFT; i = i + (2 ** (STAGE_FFT + 1))) begin : genblk1
				reg signed [31:0] idx = (m * SIZE_FFT) / (1 << (STAGE_FFT + 1));
				assign twiddle_real[(((SIZE_FFT / 2) - 1) - ((i / 2) + m)) * BIT_WIDTH+:BIT_WIDTH] = sine_wave_in[((SIZE_FFT - 1) - ((idx + (SIZE_FFT / 4)) % SIZE_FFT)) * BIT_WIDTH+:BIT_WIDTH];
				assign twiddle_imaginary[(((SIZE_FFT / 2) - 1) - ((i / 2) + m)) * BIT_WIDTH+:BIT_WIDTH] = -sine_wave_in[((SIZE_FFT - 1) - (idx % SIZE_FFT)) * BIT_WIDTH+:BIT_WIDTH];
			end
		end
	endgenerate
endmodule
`default_nettype none
module fft_cooley_tukey_helpers_Crossbar (
	recv_real,
	recv_imaginary,
	recv_val,
	recv_rdy,
	send_real,
	send_imaginary,
	send_val,
	send_rdy
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] SIZE_FFT = 8;
	parameter signed [31:0] STAGE_FFT = 0;
	parameter [0:0] FRONT = 1;
	input wire [(SIZE_FFT * BIT_WIDTH) - 1:0] recv_real;
	input wire [(SIZE_FFT * BIT_WIDTH) - 1:0] recv_imaginary;
	input wire [0:SIZE_FFT - 1] recv_val;
	output wire [0:SIZE_FFT - 1] recv_rdy;
	output wire [(SIZE_FFT * BIT_WIDTH) - 1:0] send_real;
	output wire [(SIZE_FFT * BIT_WIDTH) - 1:0] send_imaginary;
	output wire [0:SIZE_FFT - 1] send_val;
	input wire [0:SIZE_FFT - 1] send_rdy;
	genvar m;
	generate
		for (m = 0; m < (2 ** STAGE_FFT); m = m + 1) begin : genblk1
			genvar i;
			for (i = m; i < SIZE_FFT; i = i + (2 ** (STAGE_FFT + 1))) begin : genblk1
				if (FRONT == 1) begin : genblk1
					assign send_real[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[i + m] = recv_val[i];
					assign recv_rdy[i + m] = send_rdy[i];
					assign send_real[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[(i + m) + 1] = recv_val[i + (2 ** STAGE_FFT)];
					assign recv_rdy[(i + m) + 1] = send_rdy[i + (2 ** STAGE_FFT)];
				end
				else begin : genblk1
					assign send_real[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[i] = recv_val[i + m];
					assign recv_rdy[i] = send_rdy[i + m];
					assign send_real[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[i + (2 ** STAGE_FFT)] = recv_val[(i + m) + 1];
					assign recv_rdy[i + (2 ** STAGE_FFT)] = send_rdy[(i + m) + 1];
				end
			end
		end
	endgenerate
endmodule
`default_nettype none
`default_nettype none
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
module fixed_point_iterative_ComplexMultiplier (
	clk,
	reset,
	recv_val,
	recv_rdy,
	send_val,
	send_rdy,
	ar,
	ac,
	br,
	bc,
	cr,
	cc
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	input wire clk;
	input wire reset;
	input wire recv_val;
	output wire recv_rdy;
	output wire send_val;
	input wire send_rdy;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	output wire [n - 1:0] cr;
	output wire [n - 1:0] cc;
	wire mul_send_val;
	wire in_wait;
	wire [1:0] mul_stage;
	fpcmult_control #(
		.n(n),
		.d(d)
	) control(
		.clk(clk),
		.reset(reset),
		.recv_val(recv_val),
		.recv_rdy(recv_rdy),
		.send_val(send_val),
		.send_rdy(send_rdy),
		.mul_send_val(mul_send_val),
		.in_wait(in_wait),
		.mul_stage(mul_stage)
	);
	fpcmult_datapath #(
		.n(n),
		.d(d)
	) datapath(
		.clk(clk),
		.reset(reset),
		.ar(ar),
		.ac(ac),
		.br(br),
		.bc(bc),
		.cr(cr),
		.cc(cc),
		.mul_send_val(mul_send_val),
		.in_wait(in_wait),
		.mul_stage(mul_stage)
	);
endmodule
module fpcmult_control (
	clk,
	reset,
	recv_val,
	recv_rdy,
	send_val,
	send_rdy,
	mul_send_val,
	mul_stage,
	in_wait
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	input wire clk;
	input wire reset;
	input wire recv_val;
	output reg recv_rdy;
	output reg send_val;
	input wire send_rdy;
	input wire mul_send_val;
	output reg [1:0] mul_stage;
	output reg in_wait;
	reg [2:0] IDLE = 3'd0;
	reg [2:0] DONE = 3'd1;
	reg [2:0] ARBR = 3'd2;
	reg [2:0] ACBC = 3'd3;
	reg [2:0] AABB = 3'd4;
	reg [2:0] state;
	reg [2:0] next_state;
	always @(*)
		case (state)
			IDLE:
				if (recv_val)
					next_state = AABB;
				else
					next_state = IDLE;
			ARBR:
				if (mul_send_val)
					next_state = ACBC;
				else
					next_state = ARBR;
			ACBC:
				if (mul_send_val)
					next_state = DONE;
				else
					next_state = ACBC;
			AABB:
				if (mul_send_val)
					next_state = ARBR;
				else
					next_state = AABB;
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
				mul_stage = 3;
				recv_rdy = 1;
				send_val = 0;
			end
			AABB: begin
				in_wait = 0;
				mul_stage = 0;
				recv_rdy = 0;
				send_val = 0;
			end
			ARBR: begin
				in_wait = 0;
				mul_stage = 1;
				recv_rdy = 0;
				send_val = 0;
			end
			ACBC: begin
				in_wait = 0;
				mul_stage = 2;
				recv_rdy = 0;
				send_val = 0;
			end
			DONE: begin
				in_wait = 0;
				mul_stage = 3;
				recv_rdy = 0;
				send_val = 1;
			end
			default: begin
				in_wait = 0;
				mul_stage = 3;
				recv_rdy = 0;
				send_val = 0;
			end
		endcase
	always @(posedge clk)
		if (reset)
			state <= IDLE;
		else
			state <= next_state;
endmodule
module fpcmult_datapath (
	clk,
	reset,
	ar,
	ac,
	br,
	bc,
	cr,
	cc,
	in_wait,
	mul_stage,
	mul_send_val
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	input wire clk;
	input wire reset;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	output wire [n - 1:0] cr;
	output wire [n - 1:0] cc;
	input wire in_wait;
	input wire [1:0] mul_stage;
	output wire mul_send_val;
	wire [n - 1:0] c_ar;
	wire [n - 1:0] c_ac;
	wire [n - 1:0] c_br;
	wire [n - 1:0] c_bc;
	wire [n - 1:0] c_arac;
	wire [n - 1:0] i_ar;
	wire [n - 1:0] i_ac;
	wire [n - 1:0] mul_a;
	wire [n - 1:0] mul_b;
	wire [n - 1:0] mul_c;
	assign cr = c_ar - c_ac;
	assign cc = (c_arac - c_ar) - c_ac;
	cmn_EnResetReg #(.p_nbits(n)) reg_c_ar(
		.clk(clk),
		.reset(reset),
		.en(in_wait || (mul_stage == 1)),
		.d(i_ar),
		.q(c_ar)
	);
	cmn_EnResetReg #(.p_nbits(n)) reg_c_br(
		.clk(clk),
		.reset(reset),
		.en(in_wait),
		.d(br),
		.q(c_br)
	);
	cmn_EnResetReg #(.p_nbits(n)) reg_c_ac(
		.clk(clk),
		.reset(reset),
		.en(in_wait || (mul_stage == 2)),
		.d(i_ac),
		.q(c_ac)
	);
	cmn_EnResetReg #(.p_nbits(n)) reg_c_bc(
		.clk(clk),
		.reset(reset),
		.en(in_wait),
		.d(bc),
		.q(c_bc)
	);
	cmn_EnResetReg #(.p_nbits(n)) reg_c_arac(
		.clk(clk),
		.reset(reset),
		.en(mul_stage == 0),
		.d(mul_c),
		.q(c_arac)
	);
	fixed_point_iterative_Multiplier #(
		.n(n),
		.d(d),
		.sign(1)
	) multiplier(
		.clk(clk),
		.reset(reset),
		.a(mul_a),
		.b(mul_b),
		.c(mul_c),
		.recv_val(mul_stage != 3),
		.send_val(mul_send_val),
		.send_rdy(1'b1)
	);
	cmn_Mux2 #(.p_nbits(n)) iomul_ar_sel(
		.in0(ar),
		.in1(mul_c),
		.sel(~in_wait),
		.out(i_ar)
	);
	cmn_Mux2 #(.p_nbits(n)) iomul_ac_sel(
		.in0(ac),
		.in1(mul_c),
		.sel(~in_wait),
		.out(i_ac)
	);
	cmn_Mux3 #(.p_nbits(n)) mul_a_sel(
		.in0(c_ar + c_ac),
		.in1(c_ar),
		.in2(c_ac),
		.sel(mul_stage),
		.out(mul_a)
	);
	cmn_Mux3 #(.p_nbits(n)) mul_b_sel(
		.in0(c_br + c_bc),
		.in1(c_br),
		.in2(c_bc),
		.sel(mul_stage),
		.out(mul_b)
	);
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
module fixed_point_iterative_Butterfly (
	clk,
	reset,
	recv_val,
	recv_rdy,
	send_val,
	send_rdy,
	ar,
	ac,
	br,
	bc,
	wr,
	wc,
	cr,
	cc,
	dr,
	dc
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	parameter signed [7:0] mult = 0;
	input wire clk;
	input wire reset;
	input wire recv_val;
	output wire recv_rdy;
	output reg send_val;
	input wire send_rdy;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	input wire [n - 1:0] wr;
	input wire [n - 1:0] wc;
	output reg [n - 1:0] cr;
	output reg [n - 1:0] cc;
	output reg [n - 1:0] dr;
	output reg [n - 1:0] dc;
	generate
		case (mult)
			1: begin : genblk1
				reg unused = &{1'd0, wr, wc, 1'd0};
				always @(posedge clk)
					if (reset) begin
						cr <= 0;
						cc <= 0;
						dr <= 0;
						dc <= 0;
						send_val <= 0;
					end
					else if (recv_val & recv_rdy) begin
						cr <= ar + br;
						cc <= ac + bc;
						dr <= ar - br;
						dc <= ac - bc;
						send_val <= 1;
					end
					else if (send_val & send_rdy)
						send_val <= 0;
					else begin
						cr <= cr;
						cc <= cc;
						dr <= dr;
						dc <= dc;
						send_val <= send_val;
					end
				assign recv_rdy = ~send_val;
			end
			2: begin : genblk1
				reg unused = &{1'd0, wr, wc, 1'd0};
				always @(posedge clk)
					if (reset) begin
						cr <= 0;
						cc <= 0;
						dr <= 0;
						dc <= 0;
						send_val <= 0;
					end
					else if (recv_val & recv_rdy) begin
						cr <= ar - br;
						cc <= ac - bc;
						dr <= ar + br;
						dc <= ac + bc;
						send_val <= 1;
					end
					else if (send_val & send_rdy)
						send_val <= 0;
					else begin
						cr <= cr;
						cc <= cc;
						dr <= dr;
						dc <= dc;
						send_val <= send_val;
					end
				assign recv_rdy = ~send_val;
			end
			3: begin : genblk1
				reg unused = &{1'd0, wr, wc, 1'd0};
				always @(posedge clk)
					if (reset) begin
						cr <= 0;
						cc <= 0;
						dr <= 0;
						dc <= 0;
						send_val <= 0;
					end
					else if (recv_val & recv_rdy) begin
						cr <= ar - bc;
						cc <= ac + br;
						dr <= ar + bc;
						dc <= ac - br;
						send_val <= 1;
					end
					else if (send_val & send_rdy)
						send_val <= 0;
					else begin
						cr <= cr;
						cc <= cc;
						dr <= dr;
						dc <= dc;
						send_val <= send_val;
					end
				assign recv_rdy = ~send_val;
			end
			4: begin : genblk1
				reg unused = &{1'd0, wr, wc, 1'd0};
				always @(posedge clk)
					if (reset) begin
						cr <= 0;
						cc <= 0;
						dr <= 0;
						dc <= 0;
						send_val <= 0;
					end
					else if (recv_val & recv_rdy) begin
						cr <= ar + bc;
						cc <= ac - br;
						dr <= ar - bc;
						dc <= ac + br;
						send_val <= 1;
					end
					else if (send_val & send_rdy)
						send_val <= 0;
					else begin
						cr <= cr;
						cc <= cc;
						dr <= dr;
						dc <= dc;
						send_val <= send_val;
					end
				assign recv_rdy = ~send_val;
			end
			default: begin : genblk1
				wire [n - 1:0] ar_imm;
				wire [n - 1:0] ac_imm;
				wire [n - 1:0] tr;
				wire [n - 1:0] tc;
				wire [1:1] sv2v_tmp_mul_send_val;
				always @(*) send_val = sv2v_tmp_mul_send_val;
				fixed_point_iterative_ComplexMultiplier #(
					.n(n),
					.d(d)
				) mul(
					.clk(clk),
					.reset(reset),
					.ar(br),
					.ac(bc),
					.br(wr),
					.bc(wc),
					.cr(tr),
					.cc(tc),
					.recv_val(recv_val),
					.recv_rdy(recv_rdy),
					.send_val(sv2v_tmp_mul_send_val),
					.send_rdy(send_rdy)
				);
				cmn_EnResetReg #(.p_nbits(n)) ac_reg(
					.clk(clk),
					.en(recv_rdy),
					.d(ac),
					.q(ac_imm),
					.reset(reset)
				);
				cmn_EnResetReg #(.p_nbits(n)) ar_reg(
					.clk(clk),
					.en(recv_rdy),
					.d(ar),
					.q(ar_imm),
					.reset(reset)
				);
				wire [n:1] sv2v_tmp_290D2;
				assign sv2v_tmp_290D2 = ar_imm + tr;
				always @(*) cr = sv2v_tmp_290D2;
				wire [n:1] sv2v_tmp_BBFA5;
				assign sv2v_tmp_BBFA5 = ac_imm + tc;
				always @(*) cc = sv2v_tmp_BBFA5;
				wire [n:1] sv2v_tmp_EF039;
				assign sv2v_tmp_EF039 = ar_imm - tr;
				always @(*) dr = sv2v_tmp_EF039;
				wire [n:1] sv2v_tmp_CFFA2;
				assign sv2v_tmp_CFFA2 = ac_imm - tc;
				always @(*) dc = sv2v_tmp_CFFA2;
			end
		endcase
	endgenerate
endmodule
module fft_cooley_tukey_helpers_Stage (
	recv_msg_real,
	recv_msg_imag,
	recv_val,
	recv_rdy,
	send_msg_real,
	send_msg_imag,
	send_val,
	send_rdy,
	sine_wave_out,
	reset,
	clk
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] DECIMAL_PT = 16;
	parameter signed [31:0] N_SAMPLES = 8;
	parameter signed [31:0] STAGE_FFT = 0;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg_real;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg_imag;
	input wire recv_val;
	output wire recv_rdy;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg_real;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg_imag;
	output wire send_val;
	input wire send_rdy;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] sine_wave_out;
	input wire reset;
	input wire clk;
	wire [0:N_SAMPLES - 1] val_in;
	wire [0:N_SAMPLES - 1] rdy_in;
	wire [0:N_SAMPLES - 1] val_out;
	wire [0:N_SAMPLES - 1] rdy_out;
	wire [N_SAMPLES - 1:0] imm;
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign val_in[i] = recv_val;
			assign imm[i] = rdy_in[i];
		end
	endgenerate
	assign recv_rdy = imm == {N_SAMPLES {1'b1}};
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] butterfly_in_real;
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] butterfly_out_real;
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] butterfly_in_imaginary;
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] butterfly_out_imaginary;
	wire [0:N_SAMPLES - 1] val_interior_in;
	wire [0:N_SAMPLES - 1] rdy_interior_in;
	wire [0:N_SAMPLES - 1] val_interior_out;
	wire [0:N_SAMPLES - 1] rdy_interior_out;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] twiddle_real;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] twiddle_imaginary;
	wire val_interior_mini [0:(N_SAMPLES / 2) - 1];
	wire rdy_interior_mini [0:(N_SAMPLES / 2) - 1];
	fft_cooley_tukey_helpers_Crossbar #(
		.BIT_WIDTH(BIT_WIDTH),
		.SIZE_FFT(N_SAMPLES),
		.STAGE_FFT(STAGE_FFT),
		.FRONT(1)
	) xbar_in_1(
		.recv_real(recv_msg_real),
		.recv_imaginary(recv_msg_imag),
		.recv_val(val_in),
		.recv_rdy(rdy_in),
		.send_real(butterfly_in_real),
		.send_imaginary(butterfly_in_imaginary),
		.send_val(val_interior_in),
		.send_rdy(rdy_interior_in)
	);
	genvar b;
	generate
		for (b = 0; b < (N_SAMPLES / 2); b = b + 1) begin : genblk2
			localparam signed [31:0] IX = (b % (1 << STAGE_FFT)) * (N_SAMPLES / (2 * (1 << STAGE_FFT)));
			localparam signed [7:0] MMC = (IX == 0 ? 1 : (IX == (N_SAMPLES >> 1) ? 2 : (IX == (N_SAMPLES >> 2) ? 4 : (IX == (3 * (N_SAMPLES >> 2)) ? 3 : 0))));
			fixed_point_iterative_Butterfly #(
				.n(BIT_WIDTH),
				.d(DECIMAL_PT),
				.mult(MMC)
			) bfu_in(
				.ar(butterfly_in_real[((N_SAMPLES - 1) - (b * 2)) * BIT_WIDTH+:BIT_WIDTH]),
				.ac(butterfly_in_imaginary[((N_SAMPLES - 1) - (b * 2)) * BIT_WIDTH+:BIT_WIDTH]),
				.br(butterfly_in_real[((N_SAMPLES - 1) - ((b * 2) + 1)) * BIT_WIDTH+:BIT_WIDTH]),
				.bc(butterfly_in_imaginary[((N_SAMPLES - 1) - ((b * 2) + 1)) * BIT_WIDTH+:BIT_WIDTH]),
				.wr(twiddle_real[(((N_SAMPLES / 2) - 1) - b) * BIT_WIDTH+:BIT_WIDTH]),
				.wc(twiddle_imaginary[(((N_SAMPLES / 2) - 1) - b) * BIT_WIDTH+:BIT_WIDTH]),
				.recv_val(val_interior_in[b * 2] && val_interior_in[(b * 2) + 1]),
				.recv_rdy(rdy_interior_mini[b]),
				.cr(butterfly_out_real[((N_SAMPLES - 1) - (b * 2)) * BIT_WIDTH+:BIT_WIDTH]),
				.cc(butterfly_out_imaginary[((N_SAMPLES - 1) - (b * 2)) * BIT_WIDTH+:BIT_WIDTH]),
				.dr(butterfly_out_real[((N_SAMPLES - 1) - ((b * 2) + 1)) * BIT_WIDTH+:BIT_WIDTH]),
				.dc(butterfly_out_imaginary[((N_SAMPLES - 1) - ((b * 2) + 1)) * BIT_WIDTH+:BIT_WIDTH]),
				.send_rdy((send_val && rdy_interior_out[b * 2]) && rdy_interior_out[(b * 2) + 1]),
				.send_val(val_interior_mini[b]),
				.reset(reset),
				.clk(clk)
			);
			assign val_interior_out[(b * 2) + 1] = val_interior_mini[b];
			assign val_interior_out[b * 2] = val_interior_mini[b];
			assign rdy_interior_in[(b * 2) + 1] = rdy_interior_mini[b];
			assign rdy_interior_in[b * 2] = rdy_interior_mini[b];
		end
	endgenerate
	fft_cooley_tukey_helpers_Crossbar #(
		.BIT_WIDTH(BIT_WIDTH),
		.SIZE_FFT(N_SAMPLES),
		.STAGE_FFT(STAGE_FFT),
		.FRONT(0)
	) xbar_out_1(
		.recv_real(butterfly_out_real),
		.recv_imaginary(butterfly_out_imaginary),
		.recv_val(val_interior_out),
		.recv_rdy(rdy_interior_out),
		.send_real(send_msg_real),
		.send_imaginary(send_msg_imag),
		.send_val(val_out),
		.send_rdy(rdy_out)
	);
	fft_cooley_tukey_helpers_TwiddleGenerator #(
		.BIT_WIDTH(BIT_WIDTH),
		.DECIMAL_PT(DECIMAL_PT),
		.SIZE_FFT(N_SAMPLES),
		.STAGE_FFT(STAGE_FFT)
	) twiddle_generator(
		.sine_wave_in(sine_wave_out),
		.twiddle_real(twiddle_real),
		.twiddle_imaginary(twiddle_imaginary)
	);
	wire [N_SAMPLES - 1:0] imm2;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk3
			assign imm2[i] = val_out[i];
			assign rdy_out[i] = send_rdy & send_val;
		end
	endgenerate
	assign send_val = imm2 == {N_SAMPLES {1'b1}};
endmodule
