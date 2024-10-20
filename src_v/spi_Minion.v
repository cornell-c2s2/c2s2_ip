module spi_Minion (
	clk,
	reset,
	cs,
	sclk,
	mosi,
	miso,
	recv_msg,
	recv_rdy,
	recv_val,
	send_msg,
	send_rdy,
	send_val,
	minion_parity,
	adapter_parity
);
	parameter BIT_WIDTH = 32;
	parameter N_SAMPLES = 8;
	input wire clk;
	input wire reset;
	input wire cs;
	input wire sclk;
	input wire mosi;
	output wire miso;
	input wire [BIT_WIDTH - 1:0] recv_msg;
	output wire recv_rdy;
	input wire recv_val;
	output wire [BIT_WIDTH - 1:0] send_msg;
	input wire send_rdy;
	output wire send_val;
	output wire minion_parity;
	output wire adapter_parity;
	wire push_en;
	wire pull_en;
	wire [BIT_WIDTH + 1:0] push_msg;
	wire [BIT_WIDTH - 1:0] pull_msg;
	wire pull_msg_val;
	wire pull_msg_spc;
	spi_helpers_Minion_PushPull #(.nbits(BIT_WIDTH + 2)) minion(
		.clk(clk),
		.cs(cs),
		.miso(miso),
		.mosi(mosi),
		.reset(reset),
		.sclk(sclk),
		.pull_en(pull_en),
		.pull_msg({pull_msg_val, pull_msg_spc, pull_msg}),
		.push_en(push_en),
		.push_msg(push_msg),
		.parity(minion_parity)
	);
	spi_helpers_Minion_Adapter #(
		.nbits(BIT_WIDTH + 2),
		.num_entries(N_SAMPLES)
	) adapter1(
		.clk(clk),
		.reset(reset),
		.pull_en(pull_en),
		.pull_msg_val(pull_msg_val),
		.pull_msg_spc(pull_msg_spc),
		.pull_msg_data(pull_msg),
		.push_en(push_en),
		.push_msg_val_wrt(push_msg[BIT_WIDTH + 1]),
		.push_msg_val_rd(push_msg[BIT_WIDTH]),
		.push_msg_data(push_msg[BIT_WIDTH - 1:0]),
		.recv_msg(recv_msg),
		.recv_val(recv_val),
		.recv_rdy(recv_rdy),
		.send_msg(send_msg),
		.send_val(send_val),
		.send_rdy(send_rdy),
		.parity(adapter_parity)
	);
endmodule
