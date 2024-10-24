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
