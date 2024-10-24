module serdes_Deserializer (
	recv_val,
	recv_rdy,
	recv_msg,
	send_val,
	send_rdy,
	send_msg,
	clk,
	reset
);
	parameter signed [31:0] N_SAMPLES = 8;
	parameter signed [31:0] BIT_WIDTH = 32;
	input wire recv_val;
	output wire recv_rdy;
	input wire [BIT_WIDTH - 1:0] recv_msg;
	output wire send_val;
	input wire send_rdy;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg;
	input wire clk;
	input wire reset;
	generate
		if (N_SAMPLES == 1) begin : genblk1
			assign recv_rdy = send_rdy;
			assign send_val = recv_val;
			assign send_msg[(N_SAMPLES - 1) * BIT_WIDTH+:BIT_WIDTH] = recv_msg;
			reg unused = {1'b0, clk, reset, 1'b0};
		end
		else begin : genblk1
			wire [N_SAMPLES - 1:0] en_sel;
			DeserializerControl #(.N_SAMPLES(N_SAMPLES)) c(
				.recv_val(recv_val),
				.send_rdy(send_rdy),
				.send_val(send_val),
				.recv_rdy(recv_rdy),
				.reset(reset),
				.clk(clk),
				.en_sel(en_sel)
			);
			genvar i;
			for (i = 0; i < N_SAMPLES; i = i + 1) begin : l_regs
				cmn_EnResetReg #(.p_nbits(BIT_WIDTH)) register(
					.clk(clk),
					.reset(reset),
					.en(recv_rdy & en_sel[i]),
					.d(recv_msg),
					.q(send_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH])
				);
			end
		end
	endgenerate
endmodule
