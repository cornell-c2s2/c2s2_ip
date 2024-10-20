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
