module cmn_Queue (
	clk,
	reset,
	enq_val,
	enq_rdy,
	enq_msg,
	deq_val,
	deq_rdy,
	deq_msg,
	num_free_entries
);
	parameter p_type = 4'b0000;
	parameter p_msg_nbits = 1;
	parameter p_num_msgs = 2;
	parameter c_addr_nbits = $clog2(p_num_msgs);
	input wire clk;
	input wire reset;
	input wire enq_val;
	output wire enq_rdy;
	input wire [p_msg_nbits - 1:0] enq_msg;
	output wire deq_val;
	input wire deq_rdy;
	output wire [p_msg_nbits - 1:0] deq_msg;
	output wire [c_addr_nbits:0] num_free_entries;
	generate
		if (p_num_msgs == 1) begin : genblk1
			wire write_en;
			wire bypass_mux_sel;
			cmn_QueueCtrl1 #(.p_type(p_type)) ctrl(
				.clk(clk),
				.reset(reset),
				.enq_val(enq_val),
				.enq_rdy(enq_rdy),
				.deq_val(deq_val),
				.deq_rdy(deq_rdy),
				.write_en(write_en),
				.bypass_mux_sel(bypass_mux_sel),
				.num_free_entries(num_free_entries)
			);
			cmn_QueueDpath1 #(
				.p_type(p_type),
				.p_msg_nbits(p_msg_nbits)
			) dpath(
				.clk(clk),
				.reset(reset),
				.write_en(write_en),
				.bypass_mux_sel(bypass_mux_sel),
				.enq_msg(enq_msg),
				.deq_msg(deq_msg)
			);
		end
		else begin : genblk1
			wire write_en;
			wire bypass_mux_sel;
			wire [c_addr_nbits - 1:0] write_addr;
			wire [c_addr_nbits - 1:0] read_addr;
			cmn_QueueCtrl #(
				.p_type(p_type),
				.p_num_msgs(p_num_msgs)
			) ctrl(
				.clk(clk),
				.reset(reset),
				.enq_val(enq_val),
				.enq_rdy(enq_rdy),
				.deq_val(deq_val),
				.deq_rdy(deq_rdy),
				.write_en(write_en),
				.write_addr(write_addr),
				.read_addr(read_addr),
				.bypass_mux_sel(bypass_mux_sel),
				.num_free_entries(num_free_entries)
			);
			cmn_QueueDpath #(
				.p_type(p_type),
				.p_msg_nbits(p_msg_nbits),
				.p_num_msgs(p_num_msgs)
			) dpath(
				.clk(clk),
				.write_en(write_en),
				.bypass_mux_sel(bypass_mux_sel),
				.write_addr(write_addr),
				.read_addr(read_addr),
				.enq_msg(enq_msg),
				.deq_msg(deq_msg)
			);
		end
	endgenerate
endmodule
