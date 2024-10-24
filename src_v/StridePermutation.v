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
