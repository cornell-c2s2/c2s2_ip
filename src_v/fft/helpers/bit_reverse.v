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
