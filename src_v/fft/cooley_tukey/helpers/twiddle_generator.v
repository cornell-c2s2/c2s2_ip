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
