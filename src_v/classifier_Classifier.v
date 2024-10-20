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
