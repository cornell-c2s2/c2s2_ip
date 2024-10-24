module regs_shift_Bitwise (
	clk,
	reset,
	d,
	en,
	load,
	load_en,
	q
);
	parameter signed [31:0] p_nbits = 8;
	parameter [0:0] p_reset_value = 0;
	input wire clk;
	input wire reset;
	input wire d;
	input wire en;
	input wire [p_nbits - 1:0] load;
	input wire load_en;
	output reg [p_nbits - 1:0] q;
	always @(posedge clk)
		if (reset)
			q <= {p_nbits {p_reset_value}};
		else if (load_en)
			q <= load;
		else if (~load_en & en)
			q <= {q[p_nbits - 2:0], d};
		else
			q <= q;
endmodule
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
module spi_Master (
	clk,
	reset,
	spi_ifc_cs,
	spi_ifc_miso,
	spi_ifc_mosi,
	spi_ifc_sclk,
	recv_val,
	recv_rdy,
	recv_msg,
	send_val,
	send_rdy,
	send_msg,
	packet_size_ifc_val,
	packet_size_ifc_rdy,
	packet_size_ifc_msg,
	cs_addr_ifc_val,
	cs_addr_ifc_rdy,
	cs_addr_ifc_msg,
	freq_ifc_val,
	freq_ifc_rdy,
	freq_ifc_msg
);
	parameter signed [31:0] nbits = 34;
	parameter signed [31:0] ncs = 1;
	parameter signed [31:0] logBitsN = $clog2(nbits) + 1;
	parameter signed [31:0] logCSN = (ncs > 1 ? $clog2(ncs) : 1);
	input wire clk;
	input wire reset;
	output reg [0:ncs - 1] spi_ifc_cs;
	input wire spi_ifc_miso;
	output wire spi_ifc_mosi;
	output reg spi_ifc_sclk;
	input wire recv_val;
	output reg recv_rdy;
	input wire [nbits - 1:0] recv_msg;
	output reg send_val;
	input wire send_rdy;
	output wire [nbits - 1:0] send_msg;
	input wire packet_size_ifc_val;
	output wire packet_size_ifc_rdy;
	input wire [logBitsN - 1:0] packet_size_ifc_msg;
	input wire cs_addr_ifc_val;
	output wire cs_addr_ifc_rdy;
	input wire [logCSN - 1:0] cs_addr_ifc_msg;
	input wire freq_ifc_val;
	output wire freq_ifc_rdy;
	input wire [2:0] freq_ifc_msg;
	wire [logBitsN - 1:0] packet_size_reg_out;
	reg packet_size_reg_en;
	wire [logCSN - 1:0] cs_addr_reg_out;
	reg cs_addr_reg_en;
	reg [logBitsN - 1:0] sclk_counter;
	reg sclk_counter_en;
	reg [6:0] freq_high_counter;
	reg freq_high_counter_en;
	reg [6:0] freq_low_counter;
	reg freq_low_counter_en;
	wire [2:0] freq_reg_out;
	reg freq_reg_en;
	wire [nbits - 1:0] shreg_in_out;
	wire [nbits - 1:0] shreg_out_out;
	reg freq_high_refill;
	reg freq_low_refill;
	cmn_EnResetReg #(.p_nbits(logBitsN)) packet_size_reg(
		.clk(clk),
		.reset(reset),
		.q(packet_size_reg_out),
		.d(packet_size_ifc_msg),
		.en(packet_size_reg_en)
	);
	cmn_EnResetReg #(.p_nbits(logCSN)) cs_addr_reg(
		.clk(clk),
		.reset(reset),
		.q(cs_addr_reg_out),
		.d(cs_addr_ifc_msg),
		.en(cs_addr_reg_en)
	);
	cmn_EnResetReg #(.p_nbits(3)) freq_reg(
		.clk(clk),
		.reset(reset),
		.q(freq_reg_out),
		.d(freq_ifc_msg),
		.en(freq_reg_en)
	);
	assign packet_size_ifc_rdy = recv_rdy;
	assign cs_addr_ifc_rdy = recv_rdy;
	assign freq_ifc_rdy = recv_rdy;
	reg sclk_negedge;
	reg sclk_posedge;
	reg shreg_out_rst;
	reg [3:0] state;
	reg [3:0] next_state;
	always @(posedge clk) begin : up_state
		if (reset)
			state <= 4'd0;
		else
			state <= next_state;
	end
	always @(*) begin : up_stateChange
		case (state)
			4'd0: next_state = (recv_val ? 4'd1 : 4'd0);
			4'd1: next_state = 4'd2;
			4'd2: next_state = 4'd3;
			4'd3:
				if (freq_high_counter == 0)
					next_state = 4'd4;
				else
					next_state = 4'd5;
			4'd4:
				if (freq_low_counter == 0)
					next_state = (sclk_counter == 0 ? 4'd7 : 4'd3);
				else
					next_state = 4'd6;
			4'd5:
				if (freq_high_counter == 0)
					next_state = 4'd4;
				else
					next_state = 4'd5;
			4'd6:
				if (freq_low_counter == 0)
					next_state = (sclk_counter == 0 ? 4'd7 : 4'd3);
				else
					next_state = 4'd6;
			4'd7: next_state = 4'd8;
			4'd8:
				if (recv_val)
					next_state = 4'd1;
				else if (send_rdy)
					next_state = 4'd0;
				else
					next_state = 4'd8;
			default: next_state = 4'd0;
		endcase
	end
	always @(*) begin : up_stateOutputs
		recv_rdy = 0;
		send_val = 0;
		spi_ifc_sclk = 0;
		packet_size_reg_en = 0;
		cs_addr_reg_en = 0;
		begin : sv2v_autoblock_1
			integer i;
			for (i = 0; i < ncs; i = i + 1)
				spi_ifc_cs[i] = 1;
		end
		sclk_negedge = 0;
		sclk_posedge = 0;
		sclk_counter_en = 0;
		shreg_out_rst = 0;
		freq_high_refill = 0;
		freq_low_refill = 0;
		freq_high_counter_en = 0;
		freq_low_counter_en = 0;
		if (state == 4'd0) begin
			recv_rdy = 1;
			packet_size_reg_en = packet_size_ifc_val;
			cs_addr_reg_en = cs_addr_ifc_val;
			freq_reg_en = freq_ifc_val;
		end
		else if (state == 4'd1) begin
			spi_ifc_cs[cs_addr_reg_out] = 0;
			shreg_out_rst = 1;
		end
		else if (state == 4'd2) begin
			sclk_posedge = 1;
			spi_ifc_cs[cs_addr_reg_out] = 0;
		end
		else if (state == 4'd3) begin
			spi_ifc_cs[cs_addr_reg_out] = 0;
			spi_ifc_sclk = 1;
			sclk_negedge = freq_high_counter == 0;
			sclk_counter_en = 1;
			freq_high_counter_en = 1;
			freq_low_refill = 1;
		end
		else if (state == 4'd4) begin
			sclk_posedge = (sclk_counter != 0) && (freq_low_counter == 0);
			spi_ifc_cs[cs_addr_reg_out] = 0;
			spi_ifc_sclk = 0;
			freq_low_counter_en = 1;
			freq_high_refill = 1;
		end
		else if (state == 4'd5) begin
			spi_ifc_cs[cs_addr_reg_out] = 0;
			spi_ifc_sclk = 1;
			sclk_negedge = freq_high_counter == 0;
			sclk_counter_en = 0;
			freq_high_counter_en = 1;
		end
		else if (state == 4'd6) begin
			sclk_posedge = (sclk_counter != 0) && (freq_low_counter == 0);
			spi_ifc_cs[cs_addr_reg_out] = 0;
			spi_ifc_sclk = 0;
			freq_low_counter_en = 1;
		end
		else if (state == 4'd7)
			spi_ifc_cs[cs_addr_reg_out] = 0;
		else if (state == 4'd8) begin
			recv_rdy = 1;
			send_val = 1;
			packet_size_reg_en = packet_size_ifc_val;
			cs_addr_reg_en = cs_addr_ifc_val;
			freq_reg_en = freq_ifc_val;
		end
	end
	always @(posedge clk)
		if (reset)
			sclk_counter <= 0;
		else if (recv_val & recv_rdy)
			sclk_counter <= packet_size_reg_out;
		else if (sclk_counter_en)
			sclk_counter <= sclk_counter - 1;
		else
			sclk_counter <= sclk_counter;
	always @(posedge clk)
		if (reset)
			freq_high_counter <= 0;
		else if ((recv_val & recv_rdy) | freq_high_refill)
			freq_high_counter <= (2 ** freq_reg_out) - 1;
		else if (freq_high_counter_en)
			freq_high_counter <= freq_high_counter - 1;
		else
			freq_high_counter <= freq_high_counter;
	always @(posedge clk)
		if (reset)
			freq_low_counter <= 0;
		else if ((recv_val & recv_rdy) | freq_low_refill)
			freq_low_counter <= (2 ** freq_reg_out) - 1;
		else if (freq_low_counter_en)
			freq_low_counter <= freq_low_counter - 1;
		else
			freq_low_counter <= freq_low_counter;
	regs_shift_Bitwise #(
		.p_nbits(nbits),
		.p_reset_value(1'b0)
	) shreg_in(
		.clk(clk),
		.reset(shreg_out_rst),
		.d(spi_ifc_miso),
		.en(sclk_posedge),
		.load(0),
		.load_en(0),
		.q(shreg_in_out)
	);
	regs_shift_Bitwise #(
		.p_nbits(nbits),
		.p_reset_value(1'b0)
	) shreg_out(
		.clk(clk),
		.reset(reset),
		.d(0),
		.en(sclk_negedge),
		.load(recv_msg << (nbits[logBitsN - 1:0] - packet_size_reg_out)),
		.load_en(recv_rdy & recv_val),
		.q(shreg_out_out)
	);
	assign spi_ifc_mosi = shreg_out_out[nbits - 1];
	assign send_msg = shreg_in_out;
endmodule
