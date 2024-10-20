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
