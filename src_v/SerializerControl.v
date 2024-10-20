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
