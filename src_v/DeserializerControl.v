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
