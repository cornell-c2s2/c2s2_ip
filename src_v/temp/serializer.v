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
module SerializerControl (
	recv_val,
	recv_rdy,
	send_val,
	send_rdy,
	mux_sel,
	reg_en,
	clk,
	reset
);
	parameter signed [31:0] N_SAMPLES = 8;
	input wire recv_val;
	output reg recv_rdy;
	output reg send_val;
	input wire send_rdy;
	output reg [$clog2(N_SAMPLES) - 1:0] mux_sel;
	output reg reg_en;
	input wire clk;
	input wire reset;
	reg INIT = 1'b0;
	reg OUTPUT_START = 1'b1;
	reg next_state;
	reg state;
	localparam signed [31:0] NS_EXC_W = $clog2(N_SAMPLES);
	localparam signed [31:0] NS_W = $clog2(N_SAMPLES + 1);
	reg [NS_W - 1:0] mux_sel_next;
	always @(*)
		case (state)
			INIT:
				if (reset == 1)
					next_state = INIT;
				else if (recv_val == 1)
					next_state = OUTPUT_START;
				else
					next_state = INIT;
			OUTPUT_START:
				if (mux_sel_next != N_SAMPLES[NS_W - 1:0])
					next_state = OUTPUT_START;
				else
					next_state = INIT;
			default: next_state = INIT;
		endcase
	always @(*)
		case (state)
			INIT: begin
				reg_en = 1;
				send_val = 0;
				recv_rdy = 1;
				mux_sel_next = 0;
			end
			OUTPUT_START: begin
				reg_en = 0;
				send_val = 1;
				recv_rdy = 0;
				if (send_rdy == 1)
					mux_sel_next = {{NS_W - NS_EXC_W {1'b0}}, mux_sel} + 1;
				else
					mux_sel_next = {{NS_W - NS_EXC_W {1'b0}}, mux_sel};
			end
			default: begin
				reg_en = 1;
				send_val = 0;
				recv_rdy = 1;
				mux_sel_next = 0;
			end
		endcase
	always @(posedge clk)
		if (reset) begin
			state <= INIT;
			mux_sel <= 0;
		end
		else begin
			mux_sel <= mux_sel_next[NS_EXC_W - 1:0];
			state <= next_state;
		end
endmodule
