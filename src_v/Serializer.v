module serdes_Serializer (
	recv_msg,
	recv_val,
	recv_rdy,
	send_msg,
	send_val,
	send_rdy,
	reset,
	clk
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg;
	input wire recv_val;
	output wire recv_rdy;
	output wire [BIT_WIDTH - 1:0] send_msg;
	output wire send_val;
	input wire send_rdy;
	input wire reset;
	input wire clk;
	generate
		if (N_SAMPLES == 1) begin : genblk1
			assign recv_rdy = send_rdy;
			assign send_val = recv_val;
			assign send_msg = recv_msg[(N_SAMPLES - 1) * BIT_WIDTH+:BIT_WIDTH];
			reg unused = {1'b0, clk, reset, 1'b0};
		end
		else begin : genblk1
			wire [$clog2(N_SAMPLES) - 1:0] mux_sel;
			wire reg_en;
			wire [BIT_WIDTH - 1:0] reg_out [N_SAMPLES - 1:0];
			genvar i;
			for (i = 0; i < N_SAMPLES; i = i + 1) begin : l_regs
				cmn_EnResetReg #(.p_nbits(BIT_WIDTH)) register(
					.clk(clk),
					.reset(reset),
					.en(reg_en),
					.d(recv_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH]),
					.q(reg_out[i])
				);
			end
			assign send_msg = reg_out[mux_sel];
			SerializerControl #(.N_SAMPLES(N_SAMPLES)) ctrl(
				.clk(clk),
				.reset(reset),
				.recv_val(recv_val),
				.recv_rdy(recv_rdy),
				.send_val(send_val),
				.send_rdy(send_rdy),
				.mux_sel(mux_sel),
				.reg_en(reg_en)
			);
		end
	endgenerate
endmodule
