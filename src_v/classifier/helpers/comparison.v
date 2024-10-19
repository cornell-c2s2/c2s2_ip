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
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign compare_outs[i] = filtered_valid[i] & (mag_in[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] > cutoff_mag);
		end
	endgenerate
	assign compare_out = compare_outs != 0;
endmodule
