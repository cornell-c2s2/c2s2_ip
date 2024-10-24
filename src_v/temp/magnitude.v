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
