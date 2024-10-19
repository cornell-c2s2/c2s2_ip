`default_nettype none
module cmn_Reg (
	clk,
	q,
	d
);
	parameter p_nbits = 1;
	input wire clk;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	always @(posedge clk) q <= d;
endmodule
module cmn_ResetReg (
	clk,
	reset,
	q,
	d
);
	parameter p_nbits = 1;
	parameter p_reset_value = 0;
	input wire clk;
	input wire reset;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	always @(posedge clk) q <= (reset ? p_reset_value : d);
endmodule
module cmn_EnReg (
	clk,
	q,
	d,
	en
);
	parameter p_nbits = 1;
	input wire clk;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	input wire en;
	always @(posedge clk)
		if (en)
			q <= d;
endmodule
module cmn_EnResetReg (
	clk,
	reset,
	q,
	d,
	en
);
	parameter p_nbits = 1;
	parameter p_reset_value = 0;
	input wire clk;
	input wire reset;
	output reg [p_nbits - 1:0] q;
	input wire [p_nbits - 1:0] d;
	input wire en;
	function automatic signed [p_nbits - 1:0] sv2v_cast_BBED6_signed;
		input reg signed [p_nbits - 1:0] inp;
		sv2v_cast_BBED6_signed = inp;
	endfunction
	always @(posedge clk)
		if (reset || en)
			q <= (reset ? sv2v_cast_BBED6_signed(p_reset_value) : d);
endmodule
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
module DeserializerControl (
	recv_val,
	send_rdy,
	send_val,
	recv_rdy,
	en_sel,
	reset,
	clk
);
	parameter signed [31:0] N_SAMPLES = 8;
	input wire recv_val;
	input wire send_rdy;
	output reg send_val;
	output reg recv_rdy;
	output wire [N_SAMPLES - 1:0] en_sel;
	input wire reset;
	input wire clk;
	reg INIT = 1'b0;
	reg DONE = 1'b1;
	localparam signed [31:0] C_WIDTH = $clog2(N_SAMPLES) - 1;
	localparam signed [31:0] C_NXT_WIDTH = $clog2(N_SAMPLES + 1) - 1;
	reg [C_WIDTH:0] count;
	reg [C_NXT_WIDTH:0] count_next;
	reg next_state;
	reg state;
	Decoder #(.BIT_WIDTH($clog2(N_SAMPLES))) decoder(
		.in(count),
		.out(en_sel)
	);
	always @(*)
		case (state)
			INIT:
				if (count_next == N_SAMPLES[C_NXT_WIDTH:0])
					next_state = DONE;
				else
					next_state = INIT;
			DONE:
				if (send_rdy == 1)
					next_state = INIT;
				else
					next_state = DONE;
			default: next_state = INIT;
		endcase
	always @(*)
		case (state)
			INIT: begin
				if (recv_val == 1)
					count_next = {{C_NXT_WIDTH - C_WIDTH {1'b0}}, count} + 1;
				else
					count_next = {{C_NXT_WIDTH - C_WIDTH {1'b0}}, count};
				recv_rdy = 1'b1;
				send_val = 1'b0;
			end
			DONE: begin
				count_next = 0;
				recv_rdy = 1'b0;
				send_val = 1'b1;
			end
			default: begin
				count_next = 0;
				recv_rdy = 1'b1;
				send_val = 1'b0;
			end
		endcase
	always @(posedge clk)
		if (reset) begin
			count <= 0;
			state <= INIT;
		end
		else begin
			count <= count_next[$clog2(N_SAMPLES) - 1:0];
			state <= next_state;
		end
endmodule
module Decoder (
	in,
	out
);
	parameter signed [31:0] BIT_WIDTH = 3;
	input wire [BIT_WIDTH - 1:0] in;
	output wire [(1 << BIT_WIDTH) - 1:0] out;
	assign out = {{(1 << BIT_WIDTH) - 1 {1'b0}}, 1'b1} << in;
endmodule
