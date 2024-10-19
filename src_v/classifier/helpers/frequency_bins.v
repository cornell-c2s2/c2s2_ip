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
	initial if ($pow(2, LOG2_N_SAMPLES) != N_SAMPLES)
		$error("N_SAMPLES must be a power of 2");
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
