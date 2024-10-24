module arbiter_router_Arbiter (
	clk,
	reset,
	istream_val,
	istream_rdy,
	istream_msg,
	ostream_val,
	ostream_rdy,
	ostream_msg
);
	parameter signed [31:0] nbits = 32;
	parameter signed [31:0] ninputs = 3;
	localparam signed [31:0] addr_nbits = $clog2(ninputs);
	input wire clk;
	input wire reset;
	input wire [0:ninputs - 1] istream_val;
	output wire [0:ninputs - 1] istream_rdy;
	input wire [(ninputs * nbits) - 1:0] istream_msg;
	output wire ostream_val;
	input wire ostream_rdy;
	output wire [(addr_nbits + nbits) - 1:0] ostream_msg;
	reg [addr_nbits - 1:0] grants_index;
	reg [addr_nbits - 1:0] old_grants_index;
	wire [addr_nbits - 1:0] encoder_out;
	wire [nbits - 1:0] ostream_msg_data;
	wire [addr_nbits - 1:0] ostream_msg_addr;
	assign ostream_msg_data = istream_msg[((ninputs - 1) - grants_index) * nbits+:nbits];
	assign ostream_msg_addr = grants_index;
	assign ostream_val = istream_val[grants_index] & istream_rdy[grants_index];
	assign ostream_msg = {ostream_msg_addr, ostream_msg_data};
	always @(*)
		if (!istream_val[old_grants_index])
			grants_index = encoder_out;
		else
			grants_index = old_grants_index;
	genvar i;
	generate
		for (i = 0; i < ninputs; i = i + 1) begin : input_assign
			assign istream_rdy[i] = (grants_index == i[addr_nbits - 1:0] ? ostream_rdy : 1'b0);
		end
	endgenerate
	wire [addr_nbits - 1:0] encoder_outs [0:ninputs + 0];
	assign encoder_outs[ninputs] = 0;
	generate
		for (i = 0; i < ninputs; i = i + 1) begin : genblk2
			assign encoder_outs[i] = (istream_val[i] ? i : encoder_outs[i + 1]);
		end
	endgenerate
	assign encoder_out = encoder_outs[0];
	always @(posedge clk)
		if (reset)
			old_grants_index <= 0;
		else
			old_grants_index <= grants_index;
endmodule
