module cmn_QueueDpath (
	clk,
	write_en,
	bypass_mux_sel,
	write_addr,
	read_addr,
	enq_msg,
	deq_msg
);
	parameter p_type = 4'b0000;
	parameter p_msg_nbits = 4;
	parameter p_num_msgs = 2;
	parameter c_addr_nbits = $clog2(p_num_msgs);
	input wire clk;
	input wire write_en;
	input wire bypass_mux_sel;
	input wire [c_addr_nbits - 1:0] write_addr;
	input wire [c_addr_nbits - 1:0] read_addr;
	input wire [p_msg_nbits - 1:0] enq_msg;
	output wire [p_msg_nbits - 1:0] deq_msg;
	wire [p_msg_nbits - 1:0] read_data;
	cmn_Regfile_1r1w #(
		.p_data_nbits(p_msg_nbits),
		.p_num_entries(p_num_msgs)
	) qstore(
		.clk(clk),
		.read_addr(read_addr),
		.read_data(read_data),
		.write_en(write_en),
		.write_addr(write_addr),
		.write_data(enq_msg)
	);
	generate
		if (|(p_type & 4'b0010)) begin : genblk1
			cmn_Mux2 #(.p_nbits(p_msg_nbits)) bypass_mux(
				.in0(read_data),
				.in1(enq_msg),
				.sel(bypass_mux_sel),
				.out(deq_msg)
			);
		end
		else begin : genblk1
			reg unused = 1'b0 & bypass_mux_sel;
			assign deq_msg = read_data;
		end
	endgenerate
endmodule
