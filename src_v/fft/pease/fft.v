`default_nettype none
module fft_helpers_SineWave (out);
	parameter signed [31:0] N = 8;
	parameter signed [31:0] W = 32;
	parameter signed [31:0] D = 16;
	output wire [(N * W) - 1:0] out;
	localparam real PI = $acos(-1);
	generate
		if (D >= 32) begin : genblk1
			$error("D must be less than 32");
		end
	endgenerate
	genvar i;
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	generate
		for (i = 0; i < N; i = i + 1) begin : genblk2
			localparam real sinvalue = $sin(((2 * PI) * i) / N);
			reg signed [31:0] fixedptvalue = sv2v_cast_32_signed(sinvalue * (2.0 ** D));
			assign out[((N - 1) - i) * W+:W] = {{(W - D) - 1 {fixedptvalue[31]}}, fixedptvalue[D:0]};
		end
	endgenerate
endmodule
`default_nettype none
module fft_helpers_BitReverse (
	in,
	out
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] in;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] out;
	localparam signed [31:0] n = $clog2(N_SAMPLES);
	generate
		if (N_SAMPLES == 8) begin : genblk1
			assign out[(N_SAMPLES - 1) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 1) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 2) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 5) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 3) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 3) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 4) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 7) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 5) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 2) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 6) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 6) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 7) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 4) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 8) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 8) * BIT_WIDTH+:BIT_WIDTH];
		end
		else begin : genblk1
			genvar m;
			for (m = 0; m < N_SAMPLES; m = m + 1) begin : genblk1
				wire [n - 1:0] m_rev;
				genvar i;
				for (i = 0; i < n; i = i + 1) begin : genblk1
					assign m_rev[(n - i) - 1] = m[i];
				end
				assign out[((N_SAMPLES - 1) - m) * BIT_WIDTH+:BIT_WIDTH] = in[((N_SAMPLES - 1) - m_rev) * BIT_WIDTH+:BIT_WIDTH];
			end
		end
	endgenerate
endmodule
`default_nettype none
`default_nettype none
`default_nettype none
module fixed_point_combinational_Multiplier (
	a,
	b,
	c
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	parameter [0:0] sign = 1;
	input wire [n - 1:0] a;
	input wire [n - 1:0] b;
	output wire [n - 1:0] c;
	wire [(d + n) - 1:0] prod;
	wire [(d + n) - 1:0] a_ext;
	wire [(d + n) - 1:0] b_ext;
	generate
		if (sign) begin : genblk1
			assign a_ext = {{d {a[n - 1]}}, a};
			assign b_ext = {{d {b[n - 1]}}, b};
			assign prod = a_ext * b_ext;
		end
		else begin : genblk1
			assign prod = a * b;
		end
	endgenerate
	assign c = prod[(n + d) - 1:d];
	generate
		if (d > 0) begin : genblk2
			wire unused;
			assign unused = &{1'b0, prod[d - 1:0], 1'b0};
		end
	endgenerate
endmodule
module fixed_point_combinational_ComplexMultiplierS (
	ar,
	ac,
	br,
	bc,
	cr,
	cc
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	output wire [n - 1:0] cr;
	output wire [n - 1:0] cc;
	wire [n - 1:0] c_ar;
	wire [n - 1:0] c_ac;
	wire [n - 1:0] c_br;
	wire [n - 1:0] c_bc;
	wire [n - 1:0] arXbr;
	wire [n - 1:0] acXbc;
	wire [n - 1:0] arcXbrc;
	assign c_ar = ar;
	assign c_ac = ac;
	assign c_br = br;
	assign c_bc = bc;
	fixed_point_combinational_Multiplier #(
		.n(n),
		.d(d),
		.sign(1)
	) arXbrMult(
		.a(c_ar),
		.b(c_br),
		.c(arXbr)
	);
	fixed_point_combinational_Multiplier #(
		.n(n),
		.d(d),
		.sign(1)
	) acXbcMult(
		.a(c_ac),
		.b(c_bc),
		.c(acXbc)
	);
	fixed_point_combinational_Multiplier #(
		.n(n),
		.d(d),
		.sign(1)
	) arXbrcMult(
		.a(c_ar + c_ac),
		.b(c_br + c_bc),
		.c(arcXbrc)
	);
	assign cr = arXbr - acXbc;
	assign cc = (arcXbrc - arXbr) - acXbc;
endmodule
module fixed_point_combinational_ComplexMultiplier (
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
	parameter signed [31:0] num_mults = 1;
	input wire clk;
	input wire reset;
	input wire recv_val;
	output reg recv_rdy;
	output reg send_val;
	input wire send_rdy;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	output wire [n - 1:0] cr;
	output wire [n - 1:0] cc;
	reg [n - 1:0] c_ar;
	reg [n - 1:0] c_ac;
	reg [n - 1:0] c_br;
	reg [n - 1:0] c_bc;
	reg [n - 1:0] arXbr;
	reg [n - 1:0] acXbc;
	reg [n - 1:0] arcXbrc;
	generate
		if (num_mults == 3) begin : genblk1
			wire [n:1] sv2v_tmp_1272E;
			assign sv2v_tmp_1272E = ar;
			always @(*) c_ar = sv2v_tmp_1272E;
			wire [n:1] sv2v_tmp_AE874;
			assign sv2v_tmp_AE874 = ac;
			always @(*) c_ac = sv2v_tmp_AE874;
			wire [n:1] sv2v_tmp_29444;
			assign sv2v_tmp_29444 = br;
			always @(*) c_br = sv2v_tmp_29444;
			wire [n:1] sv2v_tmp_F85B2;
			assign sv2v_tmp_F85B2 = bc;
			always @(*) c_bc = sv2v_tmp_F85B2;
			wire [n:1] sv2v_tmp_arXbrMult_c;
			always @(*) arXbr = sv2v_tmp_arXbrMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrMult(
				.a(c_ar),
				.b(c_br),
				.c(sv2v_tmp_arXbrMult_c)
			);
			wire [n:1] sv2v_tmp_acXbcMult_c;
			always @(*) acXbc = sv2v_tmp_acXbcMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) acXbcMult(
				.a(c_ac),
				.b(c_bc),
				.c(sv2v_tmp_acXbcMult_c)
			);
			wire [n:1] sv2v_tmp_arXbrcMult_c;
			always @(*) arcXbrc = sv2v_tmp_arXbrcMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrcMult(
				.a(c_ar + c_ac),
				.b(c_br + c_bc),
				.c(sv2v_tmp_arXbrcMult_c)
			);
			assign cr = arXbr - acXbc;
			assign cc = (arcXbrc - arXbr) - acXbc;
			wire [1:1] sv2v_tmp_1010E;
			assign sv2v_tmp_1010E = send_rdy;
			always @(*) recv_rdy = sv2v_tmp_1010E;
			wire [1:1] sv2v_tmp_3CA7E;
			assign sv2v_tmp_3CA7E = recv_val;
			always @(*) send_val = sv2v_tmp_3CA7E;
			reg unused = &{clk, reset};
		end
		else if (num_mults == 1) begin : genblk1
			reg [2:0] IDLE = 3'd0;
			reg [2:0] MUL1 = 3'd1;
			reg [2:0] MUL2 = 3'd2;
			reg [2:0] MUL3 = 3'd3;
			reg [2:0] DONE = 3'd4;
			reg [2:0] state;
			reg [2:0] next_state;
			reg [n - 1:0] mul_a;
			reg [n - 1:0] mul_b;
			wire [n - 1:0] mul_c;
			reg unused = &{IDLE, MUL1, MUL2, MUL3, DONE};
			always @(posedge clk)
				if (reset) begin
					state <= IDLE;
					c_ar <= 0;
					c_ac <= 0;
					c_br <= 0;
					c_bc <= 0;
					arXbr <= 0;
					acXbc <= 0;
					arcXbrc <= 0;
				end
				else begin
					state <= next_state;
					if ((state == IDLE) && recv_val) begin
						c_ar <= ar;
						c_ac <= ac;
						c_br <= br;
						c_bc <= bc;
						arXbr <= 0;
						acXbc <= 0;
						arcXbrc <= 0;
					end
					else if (state == MUL1)
						arXbr <= mul_c;
					else if (state == MUL2)
						acXbc <= mul_c;
					else if (state == MUL3)
						arcXbrc <= mul_c;
				end
			always @(*) begin
				next_state = state;
				recv_rdy = 0;
				send_val = 0;
				mul_a = 0;
				mul_b = 0;
				case (state)
					IDLE: begin
						recv_rdy = 1;
						if (recv_val)
							next_state = MUL1;
						else
							next_state = IDLE;
					end
					MUL1: begin
						next_state = MUL2;
						mul_a = c_ar;
						mul_b = c_br;
					end
					MUL2: begin
						next_state = MUL3;
						mul_a = c_ac;
						mul_b = c_bc;
					end
					MUL3: begin
						next_state = DONE;
						mul_a = c_ar + c_ac;
						mul_b = c_br + c_bc;
					end
					DONE: begin
						send_val = 1;
						if (send_rdy)
							next_state = IDLE;
						else
							next_state = state;
					end
					default:
						;
				endcase
			end
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrMult(
				.a(mul_a),
				.b(mul_b),
				.c(mul_c)
			);
			assign cr = arXbr - acXbc;
			assign cc = (arcXbrc - arXbr) - acXbc;
		end
	endgenerate
endmodule
module fixed_point_combinational_Butterfly (
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
	parameter signed [31:0] b = 4;
	input wire [(b * n) - 1:0] ar;
	input wire [(b * n) - 1:0] ac;
	input wire [(b * n) - 1:0] br;
	input wire [(b * n) - 1:0] bc;
	input wire [(b * n) - 1:0] wr;
	input wire [(b * n) - 1:0] wc;
	output wire [(b * n) - 1:0] cr;
	output wire [(b * n) - 1:0] cc;
	output wire [(b * n) - 1:0] dr;
	output wire [(b * n) - 1:0] dc;
	wire [n - 1:0] m_cr [0:b - 1];
	wire [n - 1:0] m_cc [0:b - 1];
	genvar i;
	generate
		for (i = 0; i < b; i = i + 1) begin : genblk1
			fixed_point_combinational_ComplexMultiplierS #(
				.n(n),
				.d(d)
			) mult(
				.ar(wr[((b - 1) - i) * n+:n]),
				.ac(wc[((b - 1) - i) * n+:n]),
				.br(br[((b - 1) - i) * n+:n]),
				.bc(bc[((b - 1) - i) * n+:n]),
				.cr(m_cr[i]),
				.cc(m_cc[i])
			);
			assign cc[((b - 1) - i) * n+:n] = ac[((b - 1) - i) * n+:n] + m_cc[i];
			assign cr[((b - 1) - i) * n+:n] = ar[((b - 1) - i) * n+:n] + m_cr[i];
			assign dc[((b - 1) - i) * n+:n] = ac[((b - 1) - i) * n+:n] - m_cc[i];
			assign dr[((b - 1) - i) * n+:n] = ar[((b - 1) - i) * n+:n] - m_cr[i];
		end
	endgenerate
endmodule
module fft_pease_helpers_StridePermutation (
	recv,
	send
);
	parameter signed [31:0] N_SAMPLES = 8;
	parameter signed [31:0] BIT_WIDTH = 32;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send;
	genvar i;
	generate
		for (i = 0; i < (N_SAMPLES / 2); i = i + 1) begin : genblk1
			assign send[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = recv[((N_SAMPLES - 1) - (i * 2)) * BIT_WIDTH+:BIT_WIDTH];
			assign send[((N_SAMPLES - 1) - (i + (N_SAMPLES / 2))) * BIT_WIDTH+:BIT_WIDTH] = recv[((N_SAMPLES - 1) - ((i * 2) + 1)) * BIT_WIDTH+:BIT_WIDTH];
		end
	endgenerate
endmodule
module fft_pease_helpers_TwiddleGenerator (
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
	generate
		if (STAGE_FFT == 0) begin : genblk1
			genvar i;
			for (i = 0; i < (SIZE_FFT / 2); i = i + 1) begin : genblk1
				assign twiddle_real[(((SIZE_FFT / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = {{(BIT_WIDTH - DECIMAL_PT) - 1 {1'b0}}, 1'b1, {DECIMAL_PT {1'b0}}};
				assign twiddle_imaginary[(((SIZE_FFT / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = 0;
			end
			reg unused = &sine_wave_in;
		end
		else begin : genblk1
			genvar m;
			for (m = 0; m < (2 ** STAGE_FFT); m = m + 1) begin : genblk1
				genvar j;
				for (j = 0; j < (2 ** (($clog2(SIZE_FFT) - STAGE_FFT) - 1)); j = j + 1) begin : genblk1
					localparam signed [31:0] stageLeft = ($clog2(SIZE_FFT) - STAGE_FFT) - 1;
					localparam signed [31:0] idx = m * (2 ** stageLeft);
					localparam signed [31:0] si = idx + j;
					assign twiddle_real[(((SIZE_FFT / 2) - 1) - si) * BIT_WIDTH+:BIT_WIDTH] = sine_wave_in[((SIZE_FFT - 1) - (idx + (SIZE_FFT / 4))) * BIT_WIDTH+:BIT_WIDTH];
					assign twiddle_imaginary[(((SIZE_FFT / 2) - 1) - si) * BIT_WIDTH+:BIT_WIDTH] = sine_wave_in[((SIZE_FFT - 1) - (idx + (SIZE_FFT / 2))) * BIT_WIDTH+:BIT_WIDTH];
				end
			end
		end
	endgenerate
endmodule
module fft_pease_FFT (
	recv_msg,
	recv_val,
	recv_rdy,
	send_msg,
	send_val,
	send_rdy,
	reset,
	clk
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] DECIMAL_PT = 16;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg;
	input wire recv_val;
	output wire recv_rdy;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg;
	output wire send_val;
	input wire send_rdy;
	input wire reset;
	input wire clk;
	reg [2:0] IDLE = 3'd0;
	reg [2:0] COMP = 3'd1;
	reg [2:0] DONE = 3'd2;
	localparam signed [31:0] BstageBits = (N_SAMPLES > 2 ? $clog2($clog2(N_SAMPLES)) : 1);
	localparam signed [31:0] log = $clog2(N_SAMPLES) - 1;
	reg [BstageBits - 1:0] max_bstage = log[BstageBits - 1:0];
	reg [2:0] state;
	reg [2:0] next_state;
	assign recv_rdy = (state == IDLE) || (state == DONE);
	assign send_val = state == DONE;
	reg [BstageBits - 1:0] bstage;
	reg [BstageBits - 1:0] next_bstage;
	wire [(N_SAMPLES * (2 * BIT_WIDTH)) - 1:0] out_stride;
	reg [(2 * BIT_WIDTH) - 1:0] in_butterfly [0:N_SAMPLES - 1];
	wire [(N_SAMPLES * (2 * BIT_WIDTH)) - 1:0] out_butterfly;
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] reversed_msg;
	fft_helpers_BitReverse #(
		.N_SAMPLES(N_SAMPLES),
		.BIT_WIDTH(BIT_WIDTH)
	) bit_reverse(
		.in(recv_msg),
		.out(reversed_msg)
	);
	fft_pease_helpers_StridePermutation #(
		.N_SAMPLES(N_SAMPLES),
		.BIT_WIDTH(BIT_WIDTH * 2)
	) stride_permutation(
		.recv(out_butterfly),
		.send(out_stride)
	);
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] sine_wave_out;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] wr [0:$clog2(N_SAMPLES) - 1];
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] wc [0:$clog2(N_SAMPLES) - 1];
	genvar i;
	generate
		for (i = 0; i < $clog2(N_SAMPLES); i = i + 1) begin : genblk1
			fft_pease_helpers_TwiddleGenerator #(
				.BIT_WIDTH(BIT_WIDTH),
				.DECIMAL_PT(DECIMAL_PT),
				.SIZE_FFT(N_SAMPLES),
				.STAGE_FFT(i)
			) twiddle_generator(
				.sine_wave_in(sine_wave_out),
				.twiddle_real(wr[i]),
				.twiddle_imaginary(wc[i])
			);
		end
	endgenerate
	fft_helpers_SineWave #(
		.N(N_SAMPLES),
		.W(BIT_WIDTH),
		.D(DECIMAL_PT)
	) sine_wave(.out(sine_wave_out));
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] ar;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] ac;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] br;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] bc;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] cr;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] cc;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] dr;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] dc;
	generate
		for (i = 0; i < (N_SAMPLES / 2); i = i + 1) begin : genblk2
			assign ar[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[i * 2][BIT_WIDTH - 1:0];
			assign ac[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[i * 2][(2 * BIT_WIDTH) - 1:BIT_WIDTH];
			assign br[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[(i * 2) + 1][BIT_WIDTH - 1:0];
			assign bc[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[(i * 2) + 1][(2 * BIT_WIDTH) - 1:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - (i * 2)) * (2 * BIT_WIDTH)) + (BIT_WIDTH - 1)-:BIT_WIDTH] = cr[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - (i * 2)) * (2 * BIT_WIDTH)) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (2 * BIT_WIDTH) - 1 : (((2 * BIT_WIDTH) - 1) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)) - 1)-:(((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)] = cc[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - ((i * 2) + 1)) * (2 * BIT_WIDTH)) + (BIT_WIDTH - 1)-:BIT_WIDTH] = dr[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - ((i * 2) + 1)) * (2 * BIT_WIDTH)) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (2 * BIT_WIDTH) - 1 : (((2 * BIT_WIDTH) - 1) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)) - 1)-:(((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)] = dc[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
		end
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk3
			assign send_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[i][BIT_WIDTH - 1:0];
		end
	endgenerate
	fixed_point_combinational_Butterfly #(
		.n(BIT_WIDTH),
		.d(DECIMAL_PT),
		.b(N_SAMPLES / 2)
	) fft_stage(
		.wr(wr[bstage]),
		.wc(wc[bstage]),
		.ar(ar),
		.ac(ac),
		.br(br),
		.bc(bc),
		.cr(cr),
		.cc(cc),
		.dr(dr),
		.dc(dc)
	);
	always @(*) begin
		next_state = state;
		next_bstage = bstage;
		if ((state == IDLE) && recv_val)
			next_state = COMP;
		else if (state == COMP) begin
			if (bstage == max_bstage) begin
				next_state = DONE;
				next_bstage = 0;
			end
			else
				next_bstage = bstage + 1;
		end
		else if ((state == DONE) && send_rdy)
			if (recv_val)
				next_state = COMP;
			else
				next_state = IDLE;
	end
	always @(posedge clk)
		if (reset) begin
			state <= IDLE;
			bstage <= 0;
		end
		else begin
			state <= next_state;
			bstage <= next_bstage;
		end
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk4
			always @(posedge clk)
				if (reset)
					in_butterfly[i] <= 0;
				else if ((state == IDLE) || ((state == DONE) && recv_val)) begin
					in_butterfly[i][BIT_WIDTH - 1:0] <= reversed_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
					in_butterfly[i][(2 * BIT_WIDTH) - 1:BIT_WIDTH] <= 0;
				end
				else if (state == COMP)
					in_butterfly[i] <= out_stride[((N_SAMPLES - 1) - i) * (2 * BIT_WIDTH)+:2 * BIT_WIDTH];
		end
	endgenerate
endmodule
