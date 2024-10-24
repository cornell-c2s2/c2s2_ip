module wishbone_Wishbone (
	clk,
	reset,
	wbs_stb_i,
	wbs_cyc_i,
	wbs_we_i,
	wbs_sel_i,
	wbs_dat_i,
	wbs_adr_i,
	wbs_ack_o,
	wbs_dat_o,
	istream_rdy,
	istream_val,
	ostream_rdy,
	ostream_val,
	ostream_data,
	istream_data
);
	parameter signed [31:0] p_num_msgs = 2;
	parameter signed [31:0] p_num_istream = 2;
	parameter signed [31:0] p_num_ostream = 2;
	localparam signed [31:0] c_addr_nbits = $clog2(p_num_msgs);
	localparam signed [31:0] istream_addr_nbits = $clog2(p_num_istream);
	localparam signed [31:0] ostream_addr_nbits = $clog2(p_num_ostream);
	input wire clk;
	input wire reset;
	input wire wbs_stb_i;
	input wire wbs_cyc_i;
	input wire wbs_we_i;
	input wire [3:0] wbs_sel_i;
	input wire [31:0] wbs_dat_i;
	input wire [31:0] wbs_adr_i;
	output wire wbs_ack_o;
	output reg [31:0] wbs_dat_o;
	input wire [0:p_num_istream - 1] istream_rdy;
	output wire [0:p_num_istream - 1] istream_val;
	output wire [0:p_num_ostream - 1] ostream_rdy;
	input wire [0:p_num_ostream - 1] ostream_val;
	input wire [(p_num_ostream * 32) - 1:0] ostream_data;
	output wire [(p_num_istream * 32) - 1:0] istream_data;
	localparam signed [31:0] ISTREAM_BASE = 32'h30000000;
	localparam signed [31:0] OSTREAM_BASE = ISTREAM_BASE + (p_num_istream * 8);
	wire transaction_val;
	assign transaction_val = wbs_stb_i && wbs_cyc_i;
	wire [31:0] adr_sub;
	cmn_Subtractor #(.p_nbits(32)) ostream_addr_sub(
		.in0(wbs_adr_i),
		.in1(OSTREAM_BASE),
		.out(adr_sub)
	);
	wire is_check_istream;
	assign is_check_istream = ((((wbs_adr_i >= ISTREAM_BASE) && (wbs_adr_i < OSTREAM_BASE)) && (wbs_adr_i[2:0] == 3'b000)) && transaction_val) && !wbs_we_i;
	wire [istream_addr_nbits - 1:0] istream_check_ind;
	wire is_write_istream;
	assign is_write_istream = ((((wbs_adr_i >= ISTREAM_BASE) && (wbs_adr_i < OSTREAM_BASE)) && (wbs_adr_i[2:0] == 3'd4)) && transaction_val) && wbs_we_i;
	wire [istream_addr_nbits - 1:0] istream_write_ind;
	wire is_check_ostream;
	assign is_check_ostream = (((wbs_adr_i >= OSTREAM_BASE) && (wbs_adr_i[2:0] == 3'b000)) && transaction_val) && !wbs_we_i;
	wire [ostream_addr_nbits - 1:0] ostream_check_ind;
	wire is_read_ostream;
	assign is_read_ostream = (((wbs_adr_i >= OSTREAM_BASE) && (wbs_adr_i[2:0] == 3'd4)) && transaction_val) && !wbs_we_i;
	wire [ostream_addr_nbits - 1:0] ostream_read_ind;
	assign istream_check_ind = wbs_adr_i[istream_addr_nbits + 2:3];
	assign istream_write_ind = wbs_adr_i[istream_addr_nbits + 2:3];
	assign ostream_check_ind = adr_sub[ostream_addr_nbits + 2:3];
	assign ostream_read_ind = adr_sub[ostream_addr_nbits + 2:3];
	wire istream_enq_val [0:p_num_istream - 1];
	wire istream_enq_rdy [0:p_num_istream - 1];
	wire [31:0] istream_enq_msg [0:p_num_istream - 1];
	genvar i;
	generate
		for (i = 0; i < p_num_istream; i = i + 1) begin : g_istream_enq_gen
			assign istream_enq_val[i] = (is_write_istream && (istream_write_ind == i) ? 1'b1 : 1'b0);
			assign istream_enq_msg[i] = (is_write_istream && (istream_write_ind == i) ? wbs_dat_i : 32'b00000000000000000000000000000000);
		end
	endgenerate
	genvar n;
	generate
		for (n = 0; n < p_num_istream; n = n + 1) begin : g_istream_queue_gen
			cmn_Queue #(
				.p_type(4'b0000),
				.p_msg_nbits(32),
				.p_num_msgs(p_num_msgs)
			) istream_queue(
				.clk(clk),
				.reset(reset),
				.enq_val(istream_enq_val[n]),
				.enq_rdy(istream_enq_rdy[n]),
				.enq_msg(istream_enq_msg[n]),
				.deq_val(istream_val[n]),
				.deq_rdy(istream_rdy[n]),
				.deq_msg(istream_data[((p_num_istream - 1) - n) * 32+:32])
			);
		end
	endgenerate
	wire [p_num_ostream - 1:0] ostream_deq_val;
	wire [p_num_ostream - 1:0] ostream_deq_rdy;
	wire [31:0] ostream_deq_msg [0:p_num_ostream - 1];
	generate
		for (i = 0; i < p_num_ostream; i = i + 1) begin : g_ostream_enq_gen
			assign ostream_deq_rdy[i] = (is_read_ostream && (ostream_read_ind == i) ? 1'b1 : 1'b0);
		end
	endgenerate
	genvar m;
	generate
		for (m = 0; m < p_num_ostream; m = m + 1) begin : g_ostream_queue_gen
			cmn_Queue #(
				.p_type(4'b0000),
				.p_msg_nbits(32),
				.p_num_msgs(p_num_msgs)
			) ostream_queue(
				.clk(clk),
				.reset(reset),
				.enq_val(ostream_val[m]),
				.enq_rdy(ostream_rdy[m]),
				.enq_msg(ostream_data[((p_num_ostream - 1) - m) * 32+:32]),
				.deq_val(ostream_deq_val[m]),
				.deq_rdy(ostream_deq_rdy[m]),
				.deq_msg(ostream_deq_msg[m])
			);
		end
	endgenerate
	always @(*)
		if (is_check_istream)
			wbs_dat_o = {31'b0000000000000000000000000000000, istream_enq_rdy[istream_check_ind]};
		else if (is_check_ostream)
			wbs_dat_o = {31'b0000000000000000000000000000000, ostream_deq_val[ostream_check_ind]};
		else if (is_read_ostream)
			wbs_dat_o = ostream_deq_msg[ostream_read_ind];
		else
			wbs_dat_o = 32'b00000000000000000000000000000000;
	assign wbs_ack_o = 1'b1;
	reg unused = &{1'b0, wbs_sel_i, adr_sub, 1'b0};
endmodule
