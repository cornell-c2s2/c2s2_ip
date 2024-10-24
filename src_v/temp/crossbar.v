`default_nettype none
module fft_cooley_tukey_helpers_Crossbar (
	recv_real,
	recv_imaginary,
	recv_val,
	recv_rdy,
	send_real,
	send_imaginary,
	send_val,
	send_rdy
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] SIZE_FFT = 8;
	parameter signed [31:0] STAGE_FFT = 0;
	parameter [0:0] FRONT = 1;
	input wire [(SIZE_FFT * BIT_WIDTH) - 1:0] recv_real;
	input wire [(SIZE_FFT * BIT_WIDTH) - 1:0] recv_imaginary;
	input wire [0:SIZE_FFT - 1] recv_val;
	output wire [0:SIZE_FFT - 1] recv_rdy;
	output wire [(SIZE_FFT * BIT_WIDTH) - 1:0] send_real;
	output wire [(SIZE_FFT * BIT_WIDTH) - 1:0] send_imaginary;
	output wire [0:SIZE_FFT - 1] send_val;
	input wire [0:SIZE_FFT - 1] send_rdy;
	genvar m;
	generate
		for (m = 0; m < (2 ** STAGE_FFT); m = m + 1) begin : genblk1
			genvar i;
			for (i = m; i < SIZE_FFT; i = i + (2 ** (STAGE_FFT + 1))) begin : genblk1
				if (FRONT == 1) begin : genblk1
					assign send_real[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[i + m] = recv_val[i];
					assign recv_rdy[i + m] = send_rdy[i];
					assign send_real[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[(i + m) + 1] = recv_val[i + (2 ** STAGE_FFT)];
					assign recv_rdy[(i + m) + 1] = send_rdy[i + (2 ** STAGE_FFT)];
				end
				else begin : genblk1
					assign send_real[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - (i + m)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[i] = recv_val[i + m];
					assign recv_rdy[i] = send_rdy[i + m];
					assign send_real[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH] = recv_real[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_imaginary[((SIZE_FFT - 1) - (i + (2 ** STAGE_FFT))) * BIT_WIDTH+:BIT_WIDTH] = recv_imaginary[((SIZE_FFT - 1) - ((i + m) + 1)) * BIT_WIDTH+:BIT_WIDTH];
					assign send_val[i + (2 ** STAGE_FFT)] = recv_val[(i + m) + 1];
					assign recv_rdy[i + (2 ** STAGE_FFT)] = send_rdy[(i + m) + 1];
				end
			end
		end
	endgenerate
endmodule
