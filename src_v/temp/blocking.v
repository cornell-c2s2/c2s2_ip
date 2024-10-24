module crossbars_Blocking (
	recv_msg,
	recv_val,
	recv_rdy,
	send_msg,
	send_val,
	send_rdy,
	reset,
	clk,
	control,
	control_val,
	control_rdy
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_INPUTS = 2;
	parameter signed [31:0] N_OUTPUTS = 2;
	localparam signed [31:0] CONTROL_BIT_WIDTH = $clog2(N_INPUTS * N_OUTPUTS);
	input wire [(N_INPUTS * BIT_WIDTH) - 1:0] recv_msg;
	input wire [0:N_INPUTS - 1] recv_val;
	output reg [0:N_INPUTS - 1] recv_rdy;
	output reg [(N_OUTPUTS * BIT_WIDTH) - 1:0] send_msg;
	output reg [0:N_OUTPUTS - 1] send_val;
	input wire [0:N_OUTPUTS - 1] send_rdy;
	input wire reset;
	input wire clk;
	input wire [CONTROL_BIT_WIDTH - 1:0] control;
	input wire control_val;
	output wire control_rdy;
	reg [CONTROL_BIT_WIDTH - 1:0] stored_control;
	wire [$clog2(N_INPUTS) - 1:0] input_sel;
	wire [$clog2(N_OUTPUTS) - 1:0] output_sel;
	always @(posedge clk)
		if (reset)
			stored_control <= 0;
		else if (control_val)
			stored_control <= control;
		else
			stored_control <= stored_control;
	assign control_rdy = 1;
	assign input_sel = stored_control[CONTROL_BIT_WIDTH - 1:CONTROL_BIT_WIDTH - $clog2(N_INPUTS)];
	assign output_sel = stored_control[(CONTROL_BIT_WIDTH - $clog2(N_INPUTS)) - 1:(CONTROL_BIT_WIDTH - $clog2(N_INPUTS)) - $clog2(N_OUTPUTS)];
	always @(*) begin
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N_OUTPUTS; i = i + 1)
				if (i != output_sel) begin
					send_msg[((N_OUTPUTS - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = 0;
					send_val[i] = 0;
				end
				else begin
					send_msg[((N_OUTPUTS - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = recv_msg[((N_INPUTS - 1) - input_sel) * BIT_WIDTH+:BIT_WIDTH];
					send_val[i] = recv_val[input_sel];
				end
		end
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N_INPUTS; i = i + 1)
				if (i != input_sel)
					recv_rdy[i] = 0;
				else
					recv_rdy[i] = send_rdy[output_sel];
		end
	end
endmodule
