module arbiter_router_Router (
	clk,
	reset,
	istream_val,
	istream_msg,
	istream_rdy,
	ostream_val,
	ostream_msg,
	ostream_rdy
);
	parameter signed [31:0] nbits = 32;
	parameter signed [31:0] noutputs = 8;
	input wire clk;
	input wire reset;
	input wire istream_val;
	input wire [nbits - 1:0] istream_msg;
	output wire istream_rdy;
	output wire [0:noutputs - 1] ostream_val;
	output wire [(noutputs * nbits) - 1:0] ostream_msg;
	input wire [0:noutputs - 1] ostream_rdy;
	localparam signed [31:0] n_addr_bits = $clog2(noutputs);
	wire [n_addr_bits - 1:0] select;
	wire [nbits - 1:0] payload_msg;
	wire payload_val;
	wire payload_rdy;
	assign select = payload_msg[nbits - 1:nbits - n_addr_bits];
	wire [2:0] num_free_entries;
	cmn_Queue #(
		.p_msg_nbits(nbits),
		.p_num_msgs(3)
	) queue_inst(
		.clk(clk),
		.reset(reset),
		.enq_val(istream_val),
		.enq_rdy(istream_rdy),
		.enq_msg(istream_msg),
		.deq_val(payload_val),
		.deq_rdy(payload_rdy),
		.deq_msg(payload_msg),
		.num_free_entries(num_free_entries)
	);
	cmn_MuxN #(
		.nbits(1),
		.ninputs(noutputs)
	) mux_inst(
		.in(ostream_rdy),
		.sel(select),
		.out(payload_rdy)
	);
	cmn_DemuxN #(
		.nbits(1),
		.noutputs(noutputs)
	) demux_inst(
		.in(payload_val),
		.sel(select),
		.out(ostream_val)
	);
	genvar i;
	generate
		for (i = 0; i < noutputs; i = i + 1) begin : output_gen
			assign ostream_msg[((noutputs - 1) - i) * nbits+:nbits] = payload_msg;
		end
	endgenerate
	reg unused = &{1'b0, num_free_entries, 1'b0};
endmodule
