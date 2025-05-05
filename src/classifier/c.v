`default_nettype none
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
`default_nettype none
module magnitude_Magnitude (
	recv_msg,
	send_msg
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire signed [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg;
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign send_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = (recv_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] < 0 ? -recv_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] : recv_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH]);
		end
	endgenerate
endmodule
`default_nettype none
module highpass_Highpass (
	cutoff_freq,
	freq_in,
	filtered_valid
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [BIT_WIDTH - 1:0] cutoff_freq;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] freq_in;
	output wire [0:N_SAMPLES - 1] filtered_valid;
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign filtered_valid[i] = freq_in[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] > cutoff_freq;
		end
	endgenerate
endmodule
`default_nettype none
module classifier_helpers_FrequencyBins (
	sampling_freq,
	frequency_out
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 16;
	input wire [BIT_WIDTH - 1:0] sampling_freq;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] frequency_out;
	localparam signed [31:0] LOG2_N_SAMPLES = $clog2(N_SAMPLES);
	// initial if ($pow(2, LOG2_N_SAMPLES) != N_SAMPLES)
	// 	$error("N_SAMPLES must be a power of 2");
	function automatic signed [LOG2_N_SAMPLES - 1:0] sv2v_cast_B215B_signed;
		input reg signed [LOG2_N_SAMPLES - 1:0] inp;
		sv2v_cast_B215B_signed = inp;
	endfunction
	wire [(LOG2_N_SAMPLES + BIT_WIDTH) - 1:0] wide_sampling_freq = {sv2v_cast_B215B_signed(0), sampling_freq};
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : gen_freq
			wire [(LOG2_N_SAMPLES + BIT_WIDTH) - 1:0] wide_freq_out = (i * wide_sampling_freq) >> (LOG2_N_SAMPLES + 1);
			assign frequency_out[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = wide_freq_out[BIT_WIDTH - 1:0];
			wire unused = &{1'b0, wide_freq_out[(LOG2_N_SAMPLES + BIT_WIDTH) - 1:BIT_WIDTH], 1'b0};
		end
	endgenerate
endmodule
`default_nettype none
module comparison_Comparison (
	cutoff_mag,
	filtered_valid,
	mag_in,
	compare_out
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [BIT_WIDTH - 1:0] cutoff_mag;
	input wire [0:N_SAMPLES - 1] filtered_valid;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] mag_in;
	output wire compare_out;
	wire [N_SAMPLES - 1:0] compare_outs;
	wire magnitude_val [0:N_SAMPLES - 1];
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign magnitude_val[i] = mag_in[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] > cutoff_mag;
			assign compare_outs[i] = filtered_valid[i] & (mag_in[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] > cutoff_mag);
		end
	endgenerate
	assign compare_out = compare_outs != 0;
endmodule
module classifier_Classifier (
	clk,
	reset,
	recv_rdy,
	recv_val,
	recv_msg,
	cutoff_freq_rdy,
	cutoff_freq_val,
	cutoff_freq_msg,
	cutoff_mag_rdy,
	cutoff_mag_val,
	cutoff_mag_msg,
	sampling_freq_rdy,
	sampling_freq_val,
	sampling_freq_msg,
	send_rdy,
	send_val,
	send_msg
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] DECIMAL_PT = 16;
	parameter signed [31:0] FREQ_BIT_WIDTH = 16;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire clk;
	input wire reset;
	output wire recv_rdy;
	input wire recv_val;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg;
	output wire cutoff_freq_rdy;
	input wire cutoff_freq_val;
	input wire [FREQ_BIT_WIDTH - 1:0] cutoff_freq_msg;
	output wire cutoff_mag_rdy;
	input wire cutoff_mag_val;
	input wire [BIT_WIDTH - 1:0] cutoff_mag_msg;
	output wire sampling_freq_rdy;
	input wire sampling_freq_val;
	input wire [FREQ_BIT_WIDTH - 1:0] sampling_freq_msg;
	input wire send_rdy;
	output wire send_val;
	output wire send_msg;
	wire [FREQ_BIT_WIDTH - 1:0] in_cutoff_freq;
	wire [BIT_WIDTH - 1:0] in_cutoff_mag;
	wire [FREQ_BIT_WIDTH - 1:0] in_sampling_freq;
	cmn_EnResetReg #(
		.p_nbits(FREQ_BIT_WIDTH),
		.p_reset_value(0)
	) cutoff_freq_in(
		.clk(clk),
		.reset(reset),
		.d(cutoff_freq_msg),
		.q(in_cutoff_freq),
		.en(cutoff_freq_val)
	);
	assign cutoff_freq_rdy = 1;
	cmn_EnResetReg #(
		.p_nbits(BIT_WIDTH),
		.p_reset_value(0)
	) cutoff_mag_in(
		.clk(clk),
		.reset(reset),
		.d(cutoff_mag_msg),
		.q(in_cutoff_mag),
		.en(cutoff_mag_val)
	);
	assign cutoff_mag_rdy = 1;
	cmn_EnResetReg #(
		.p_nbits(FREQ_BIT_WIDTH),
		.p_reset_value(0)
	) sampling_freq_in(
		.clk(clk),
		.reset(reset),
		.d(sampling_freq_msg),
		.q(in_sampling_freq),
		.en(sampling_freq_val)
	);
	assign sampling_freq_rdy = 1;
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] out_mag;
	magnitude_Magnitude #(
		.BIT_WIDTH(BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) mag_calc(
		.recv_msg(recv_msg),
		.send_msg(out_mag)
	);
	wire [(N_SAMPLES * FREQ_BIT_WIDTH) - 1:0] frequency_array;
	classifier_helpers_FrequencyBins #(
		.BIT_WIDTH(FREQ_BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) freq_gen(
		.sampling_freq(in_sampling_freq),
		.frequency_out(frequency_array)
	);
	wire [0:N_SAMPLES - 1] out_filter;
	highpass_Highpass #(
		.BIT_WIDTH(FREQ_BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) highpass_fil(
		.cutoff_freq(in_cutoff_freq),
		.freq_in(frequency_array),
		.filtered_valid(out_filter)
	);
	wire out_comparison;
	comparison_Comparison #(
		.BIT_WIDTH(BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) comparison(
		.cutoff_mag(in_cutoff_mag),
		.filtered_valid(out_filter),
		.mag_in(out_mag),
		.compare_out(out_comparison)
	);
	assign send_msg = out_comparison;
	assign send_val = recv_val;
	assign recv_rdy = send_rdy;
endmodule
