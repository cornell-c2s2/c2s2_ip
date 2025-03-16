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
module cmn_Mux2 (
	in0,
	in1,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			1'd0: out = in0;
			1'd1: out = in1;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux3 (
	in0,
	in1,
	in2,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [1:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			2'd0: out = in0;
			2'd1: out = in1;
			2'd2: out = in2;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux4 (
	in0,
	in1,
	in2,
	in3,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [1:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			2'd0: out = in0;
			2'd1: out = in1;
			2'd2: out = in2;
			2'd3: out = in3;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux5 (
	in0,
	in1,
	in2,
	in3,
	in4,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux6 (
	in0,
	in1,
	in2,
	in3,
	in4,
	in5,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [p_nbits - 1:0] in5;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			3'd5: out = in5;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux7 (
	in0,
	in1,
	in2,
	in3,
	in4,
	in5,
	in6,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [p_nbits - 1:0] in5;
	input wire [p_nbits - 1:0] in6;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			3'd5: out = in5;
			3'd6: out = in6;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_Mux8 (
	in0,
	in1,
	in2,
	in3,
	in4,
	in5,
	in6,
	in7,
	sel,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire [p_nbits - 1:0] in2;
	input wire [p_nbits - 1:0] in3;
	input wire [p_nbits - 1:0] in4;
	input wire [p_nbits - 1:0] in5;
	input wire [p_nbits - 1:0] in6;
	input wire [p_nbits - 1:0] in7;
	input wire [2:0] sel;
	output reg [p_nbits - 1:0] out;
	always @(*)
		case (sel)
			3'd0: out = in0;
			3'd1: out = in1;
			3'd2: out = in2;
			3'd3: out = in3;
			3'd4: out = in4;
			3'd5: out = in5;
			3'd6: out = in6;
			3'd7: out = in7;
			default: out = {p_nbits {1'bx}};
		endcase
endmodule
module cmn_MuxN (
	in,
	sel,
	out
);
	parameter nbits = 1;
	parameter ninputs = 2;
	input wire [(ninputs * nbits) - 1:0] in;
	input wire [$clog2(ninputs) - 1:0] sel;
	output wire [nbits - 1:0] out;
	assign out = in[((ninputs - 1) - sel) * nbits+:nbits];
endmodule
module cmn_Regfile_1r1w (
	clk,
	read_addr,
	read_data,
	write_en,
	write_addr,
	write_data
);
	parameter p_data_nbits = 1;
	parameter p_num_entries = 2;
	parameter c_addr_nbits = $clog2(p_num_entries);
	input wire clk;
	input wire [c_addr_nbits - 1:0] read_addr;
	output wire [p_data_nbits - 1:0] read_data;
	input wire write_en;
	input wire [c_addr_nbits - 1:0] write_addr;
	input wire [p_data_nbits - 1:0] write_data;
	reg [p_data_nbits - 1:0] rfile [p_num_entries - 1:0];
	assign read_data = rfile[read_addr];
	always @(posedge clk)
		if (write_en)
			rfile[write_addr] <= write_data;
endmodule
module cmn_ResetRegfile_1r1w (
	clk,
	reset,
	read_addr,
	read_data,
	write_en,
	write_addr,
	write_data
);
	parameter p_data_nbits = 1;
	parameter p_num_entries = 2;
	parameter p_reset_value = 0;
	parameter c_addr_nbits = $clog2(p_num_entries);
	input wire clk;
	input wire reset;
	input wire [c_addr_nbits - 1:0] read_addr;
	output wire [p_data_nbits - 1:0] read_data;
	input wire write_en;
	input wire [c_addr_nbits - 1:0] write_addr;
	input wire [p_data_nbits - 1:0] write_data;
	reg [p_data_nbits - 1:0] rfile [p_num_entries - 1:0];
	assign read_data = rfile[read_addr];
	genvar i;
	generate
		for (i = 0; i < p_num_entries; i = i + 1) begin : wport
			always @(posedge clk)
				if (reset)
					rfile[i] <= p_reset_value;
				else if (write_en && (i[c_addr_nbits - 1:0] == write_addr))
					rfile[i] <= write_data;
		end
	endgenerate
endmodule
module cmn_Regfile_2r1w (
	clk,
	read_addr0,
	read_data0,
	read_addr1,
	read_data1,
	write_en,
	write_addr,
	write_data
);
	parameter p_data_nbits = 1;
	parameter p_num_entries = 2;
	parameter c_addr_nbits = $clog2(p_num_entries);
	input wire clk;
	input wire [c_addr_nbits - 1:0] read_addr0;
	output wire [p_data_nbits - 1:0] read_data0;
	input wire [c_addr_nbits - 1:0] read_addr1;
	output wire [p_data_nbits - 1:0] read_data1;
	input wire write_en;
	input wire [c_addr_nbits - 1:0] write_addr;
	input wire [p_data_nbits - 1:0] write_data;
	reg [p_data_nbits - 1:0] rfile [p_num_entries - 1:0];
	assign read_data0 = rfile[read_addr0];
	assign read_data1 = rfile[read_addr1];
	always @(posedge clk)
		if (write_en)
			rfile[write_addr] <= write_data;
endmodule
module cmn_Regfile_2r2w (
	clk,
	read_addr0,
	read_data0,
	read_addr1,
	read_data1,
	write_en0,
	write_addr0,
	write_data0,
	write_en1,
	write_addr1,
	write_data1
);
	parameter p_data_nbits = 1;
	parameter p_num_entries = 2;
	parameter c_addr_nbits = $clog2(p_num_entries);
	input wire clk;
	input wire [c_addr_nbits - 1:0] read_addr0;
	output wire [p_data_nbits - 1:0] read_data0;
	input wire [c_addr_nbits - 1:0] read_addr1;
	output wire [p_data_nbits - 1:0] read_data1;
	input wire write_en0;
	input wire [c_addr_nbits - 1:0] write_addr0;
	input wire [p_data_nbits - 1:0] write_data0;
	input wire write_en1;
	input wire [c_addr_nbits - 1:0] write_addr1;
	input wire [p_data_nbits - 1:0] write_data1;
	reg [p_data_nbits - 1:0] rfile [p_num_entries - 1:0];
	assign read_data0 = rfile[read_addr0];
	assign read_data1 = rfile[read_addr1];
	always @(posedge clk) begin
		if (write_en0)
			rfile[write_addr0] <= write_data0;
		if (write_en1)
			rfile[write_addr1] <= write_data1;
	end
endmodule
module cmn_Regfile_2r1w_zero (
	clk,
	rd_addr0,
	rd_data0,
	rd_addr1,
	rd_data1,
	wr_en,
	wr_addr,
	wr_data
);
	input wire clk;
	input wire [4:0] rd_addr0;
	output wire [31:0] rd_data0;
	input wire [4:0] rd_addr1;
	output wire [31:0] rd_data1;
	input wire wr_en;
	input wire [4:0] wr_addr;
	input wire [31:0] wr_data;
	wire [31:0] rf_read_data0;
	wire [31:0] rf_read_data1;
	cmn_Regfile_2r1w #(
		.p_data_nbits(32),
		.p_num_entries(32)
	) r_file(
		.clk(clk),
		.read_addr0(rd_addr0),
		.read_data0(rf_read_data0),
		.read_addr1(rd_addr1),
		.read_data1(rf_read_data1),
		.write_en(wr_en),
		.write_addr(wr_addr),
		.write_data(wr_data)
	);
	assign rd_data0 = (rd_addr0 == 5'd0 ? 32'd0 : rf_read_data0);
	assign rd_data1 = (rd_addr1 == 5'd0 ? 32'd0 : rf_read_data1);
endmodule
module cmn_QueueCtrl1 (
	clk,
	reset,
	enq_val,
	enq_rdy,
	deq_val,
	deq_rdy,
	write_en,
	bypass_mux_sel,
	num_free_entries
);
	parameter p_type = 4'b0000;
	input wire clk;
	input wire reset;
	input wire enq_val;
	output wire enq_rdy;
	output wire deq_val;
	input wire deq_rdy;
	output wire write_en;
	output wire bypass_mux_sel;
	output wire num_free_entries;
	reg full;
	wire full_next;
	always @(posedge clk) full <= (reset ? 1'b0 : full_next);
	assign num_free_entries = (full ? 1'b0 : 1'b1);
	localparam c_pipe_en = |(p_type & 4'b0001);
	localparam c_bypass_en = |(p_type & 4'b0010);
	wire do_enq;
	assign do_enq = enq_rdy && enq_val;
	wire do_deq;
	assign do_deq = deq_rdy && deq_val;
	wire empty;
	assign empty = ~full;
	wire do_pipe;
	assign do_pipe = ((c_pipe_en && full) && do_enq) && do_deq;
	wire do_bypass;
	assign do_bypass = ((c_bypass_en && empty) && do_enq) && do_deq;
	assign write_en = do_enq && ~do_bypass;
	assign bypass_mux_sel = empty;
	assign enq_rdy = ~full || ((c_pipe_en && full) && deq_rdy);
	assign deq_val = ~empty || ((c_bypass_en && empty) && enq_val);
	assign full_next = (do_deq && ~do_pipe ? 1'b0 : (do_enq && ~do_bypass ? 1'b1 : full));
endmodule
module cmn_QueueDpath1 (
	clk,
	reset,
	write_en,
	bypass_mux_sel,
	enq_msg,
	deq_msg
);
	parameter p_type = 4'b0000;
	parameter p_msg_nbits = 1;
	input wire clk;
	input wire reset;
	input wire write_en;
	input wire bypass_mux_sel;
	input wire [p_msg_nbits - 1:0] enq_msg;
	output wire [p_msg_nbits - 1:0] deq_msg;
	wire [p_msg_nbits - 1:0] qstore;
	cmn_EnResetReg #(.p_nbits(p_msg_nbits)) qstore_reg(
		.clk(clk),
		.reset(reset),
		.en(write_en),
		.d(enq_msg),
		.q(qstore)
	);
	generate
		if (|(p_type & 4'b0010)) begin : genblk1
			cmn_Mux2 #(.p_nbits(p_msg_nbits)) bypass_mux(
				.in0(qstore),
				.in1(enq_msg),
				.sel(bypass_mux_sel),
				.out(deq_msg)
			);
		end
		else begin : genblk1
			reg unused = &{1'b0, bypass_mux_sel, 1'b0};
			assign deq_msg = qstore;
		end
	endgenerate
endmodule
module cmn_QueueCtrl (
	clk,
	reset,
	enq_val,
	enq_rdy,
	deq_val,
	deq_rdy,
	write_en,
	write_addr,
	read_addr,
	bypass_mux_sel,
	num_free_entries
);
	parameter p_type = 4'b0000;
	parameter p_num_msgs = 2;
	parameter c_addr_nbits = $clog2(p_num_msgs);
	input wire clk;
	input wire reset;
	input wire enq_val;
	output wire enq_rdy;
	output wire deq_val;
	input wire deq_rdy;
	output wire write_en;
	output wire [c_addr_nbits - 1:0] write_addr;
	output wire [c_addr_nbits - 1:0] read_addr;
	output wire bypass_mux_sel;
	output wire [c_addr_nbits:0] num_free_entries;
	wire [c_addr_nbits - 1:0] enq_ptr;
	wire [c_addr_nbits - 1:0] enq_ptr_next;
	cmn_ResetReg #(.p_nbits(c_addr_nbits)) enq_ptr_reg(
		.clk(clk),
		.reset(reset),
		.d(enq_ptr_next),
		.q(enq_ptr)
	);
	wire [c_addr_nbits - 1:0] deq_ptr;
	wire [c_addr_nbits - 1:0] deq_ptr_next;
	cmn_ResetReg #(.p_nbits(c_addr_nbits)) deq_ptr_reg(
		.clk(clk),
		.reset(reset),
		.d(deq_ptr_next),
		.q(deq_ptr)
	);
	assign write_addr = enq_ptr;
	assign read_addr = deq_ptr;
	wire full;
	wire full_next;
	cmn_ResetReg #(.p_nbits(1)) full_reg(
		.clk(clk),
		.reset(reset),
		.d(full_next),
		.q(full)
	);
	localparam c_pipe_en = |(p_type & 4'b0001);
	localparam c_bypass_en = |(p_type & 4'b0010);
	wire do_enq;
	assign do_enq = enq_rdy && enq_val;
	wire do_deq;
	assign do_deq = deq_rdy && deq_val;
	wire empty;
	assign empty = ~full && (enq_ptr == deq_ptr);
	wire do_pipe;
	assign do_pipe = ((c_pipe_en && full) && do_enq) && do_deq;
	wire do_bypass;
	assign do_bypass = ((c_bypass_en && empty) && do_enq) && do_deq;
	assign write_en = do_enq && ~do_bypass;
	assign bypass_mux_sel = empty;
	assign enq_rdy = ~full || ((c_pipe_en && full) && deq_rdy);
	assign deq_val = ~empty || ((c_bypass_en && empty) && enq_val);
	wire [c_addr_nbits - 1:0] deq_ptr_plus1;
	assign deq_ptr_plus1 = deq_ptr + 1'b1;
	wire [c_addr_nbits - 1:0] deq_ptr_inc;
	assign deq_ptr_inc = (deq_ptr_plus1 == p_num_msgs ? {c_addr_nbits {1'b0}} : deq_ptr_plus1);
	wire [c_addr_nbits - 1:0] enq_ptr_plus1;
	assign enq_ptr_plus1 = enq_ptr + 1'b1;
	wire [c_addr_nbits - 1:0] enq_ptr_inc;
	assign enq_ptr_inc = (enq_ptr_plus1 == p_num_msgs ? {c_addr_nbits {1'b0}} : enq_ptr_plus1);
	assign deq_ptr_next = (do_deq && ~do_bypass ? deq_ptr_inc : deq_ptr);
	assign enq_ptr_next = (do_enq && ~do_bypass ? enq_ptr_inc : enq_ptr);
	assign full_next = ((do_enq && ~do_deq) && (enq_ptr_inc == deq_ptr) ? 1'b1 : ((do_deq && full) && ~do_pipe ? 1'b0 : full));
	assign num_free_entries = (full ? {c_addr_nbits + 1 {1'b0}} : (empty ? p_num_msgs[c_addr_nbits:0] : (enq_ptr > deq_ptr ? p_num_msgs[c_addr_nbits:0] - (enq_ptr - deq_ptr) : (deq_ptr > enq_ptr ? deq_ptr - enq_ptr : {c_addr_nbits + 1 {1'bx}}))));
endmodule
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
module spi_helpers_Minion_Adapter (
	clk,
	reset,
	pull_en,
	pull_msg_val,
	pull_msg_spc,
	pull_msg_data,
	push_en,
	push_msg_val_wrt,
	push_msg_val_rd,
	push_msg_data,
	recv_msg,
	recv_rdy,
	recv_val,
	send_msg,
	send_rdy,
	send_val,
	parity
);
	parameter signed [31:0] nbits = 8;
	parameter signed [31:0] num_entries = 1;
	input wire clk;
	input wire reset;
	input wire pull_en;
	output reg pull_msg_val;
	output reg pull_msg_spc;
	output reg [nbits - 3:0] pull_msg_data;
	input wire push_en;
	input wire push_msg_val_wrt;
	input wire push_msg_val_rd;
	input wire [nbits - 3:0] push_msg_data;
	input wire [nbits - 3:0] recv_msg;
	output wire recv_rdy;
	input wire recv_val;
	output wire [nbits - 3:0] send_msg;
	input wire send_rdy;
	output wire send_val;
	output wire parity;
	reg open_entries;
	wire [nbits - 3:0] cm_q_send_msg;
	reg cm_q_send_rdy;
	wire cm_q_send_val;
	wire [$clog2(num_entries):0] unused;
	cmn_Queue #(
		.p_type(4'b0000),
		.p_msg_nbits(nbits - 2),
		.p_num_msgs(num_entries)
	) cm_q(
		.clk(clk),
		.num_free_entries(unused),
		.reset(reset),
		.enq_msg(recv_msg),
		.enq_rdy(recv_rdy),
		.enq_val(recv_val),
		.deq_msg(cm_q_send_msg),
		.deq_rdy(cm_q_send_rdy),
		.deq_val(cm_q_send_val)
	);
	wire [$clog2(num_entries):0] mc_q_num_free;
	wire mc_q_recv_rdy;
	reg mc_q_recv_val;
	cmn_Queue #(
		.p_type(4'b0000),
		.p_msg_nbits(nbits - 2),
		.p_num_msgs(num_entries)
	) mc_q(
		.clk(clk),
		.num_free_entries(mc_q_num_free),
		.reset(reset),
		.enq_msg(push_msg_data),
		.enq_rdy(mc_q_recv_rdy),
		.enq_val(mc_q_recv_val),
		.deq_msg(send_msg),
		.deq_rdy(send_rdy),
		.deq_val(send_val)
	);
	assign parity = ^send_msg & send_val;
	always @(*) begin : comb_block
		open_entries = mc_q_num_free > 1;
		mc_q_recv_val = push_msg_val_wrt & push_en;
		pull_msg_spc = mc_q_recv_rdy & (~mc_q_recv_val | open_entries);
		cm_q_send_rdy = push_msg_val_rd & pull_en;
		pull_msg_val = cm_q_send_rdy & cm_q_send_val;
		pull_msg_data = cm_q_send_msg & {nbits - 2 {pull_msg_val}};
	end
endmodule
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
module spi_helpers_Synchronizer (
	clk,
	reset,
	in_,
	posedge_,
	negedge_,
	out
);
	parameter [0:0] reset_value = 0;
	input wire clk;
	input wire reset;
	input wire in_;
	output reg posedge_;
	output reg negedge_;
	output wire out;
	reg [2:0] shreg;
	always @(*) begin
		posedge_ = ~shreg[2] & shreg[1];
		negedge_ = shreg[2] & ~shreg[1];
	end
	always @(posedge clk)
		if (reset)
			shreg <= {3 {reset_value}};
		else
			shreg <= {shreg[1:0], in_};
	assign out = shreg[1];
endmodule
module spi_helpers_Minion_PushPull (
	clk,
	cs,
	miso,
	mosi,
	reset,
	sclk,
	pull_en,
	pull_msg,
	push_en,
	push_msg,
	parity
);
	parameter signed [31:0] nbits = 8;
	input wire clk;
	input wire cs;
	output wire miso;
	input wire mosi;
	input wire reset;
	input wire sclk;
	output wire pull_en;
	input wire [nbits - 1:0] pull_msg;
	output wire push_en;
	output wire [nbits - 1:0] push_msg;
	output wire parity;
	wire cs_sync_clk;
	wire cs_sync_in_;
	wire cs_sync_negedge_;
	wire cs_sync_out;
	wire cs_sync_posedge_;
	wire cs_sync_reset;
	spi_helpers_Synchronizer #(.reset_value(1'b1)) cs_sync(
		.clk(cs_sync_clk),
		.in_(cs_sync_in_),
		.negedge_(cs_sync_negedge_),
		.out(cs_sync_out),
		.posedge_(cs_sync_posedge_),
		.reset(cs_sync_reset)
	);
	wire mosi_sync_clk;
	wire mosi_sync_in_;
	wire mosi_sync_out;
	wire mosi_sync_negedge_;
	wire mosi_sync_posedge_;
	wire mosi_sync_reset;
	spi_helpers_Synchronizer #(.reset_value(1'b0)) mosi_sync(
		.clk(mosi_sync_clk),
		.in_(mosi_sync_in_),
		.negedge_(mosi_sync_negedge_),
		.out(mosi_sync_out),
		.posedge_(mosi_sync_posedge_),
		.reset(mosi_sync_reset)
	);
	wire sclk_sync_clk;
	wire sclk_sync_in_;
	wire sclk_sync_negedge_;
	wire sclk_sync_out;
	wire sclk_sync_posedge_;
	wire sclk_sync_reset;
	spi_helpers_Synchronizer #(.reset_value(1'b0)) sclk_sync(
		.clk(sclk_sync_clk),
		.in_(sclk_sync_in_),
		.negedge_(sclk_sync_negedge_),
		.out(sclk_sync_out),
		.posedge_(sclk_sync_posedge_),
		.reset(sclk_sync_reset)
	);
	wire shreg_in_clk;
	wire shreg_in_in_;
	wire [nbits - 1:0] shreg_in_load_data;
	wire shreg_in_load_en;
	wire [nbits - 1:0] shreg_in_out;
	wire shreg_in_reset;
	reg shreg_in_shift_en;
	regs_shift_Bitwise #(.p_nbits(nbits)) shreg_in(
		.clk(shreg_in_clk),
		.reset(shreg_in_reset),
		.d(shreg_in_in_),
		.en(shreg_in_shift_en),
		.load(shreg_in_load_data),
		.load_en(shreg_in_load_en),
		.q(shreg_in_out)
	);
	wire shreg_out_clk;
	wire shreg_out_in_;
	wire [nbits - 1:0] shreg_out_load_data;
	wire shreg_out_load_en;
	wire [nbits - 1:0] shreg_out_out;
	wire shreg_out_reset;
	reg shreg_out_shift_en;
	regs_shift_Bitwise #(.p_nbits(nbits)) shreg_out(
		.clk(shreg_out_clk),
		.reset(shreg_out_reset),
		.d(shreg_out_in_),
		.en(shreg_out_shift_en),
		.load(shreg_out_load_data),
		.load_en(shreg_out_load_en),
		.q(shreg_out_out)
	);
	always @(*) begin
		shreg_in_shift_en = ~cs_sync_out & sclk_sync_posedge_;
		shreg_out_shift_en = ~cs_sync_out & sclk_sync_negedge_;
	end
	assign cs_sync_clk = clk;
	assign cs_sync_reset = reset;
	assign cs_sync_in_ = cs;
	assign sclk_sync_clk = clk;
	assign sclk_sync_reset = reset;
	assign sclk_sync_in_ = sclk;
	assign mosi_sync_clk = clk;
	assign mosi_sync_reset = reset;
	assign mosi_sync_in_ = mosi;
	assign shreg_in_clk = clk;
	assign shreg_in_reset = reset;
	assign shreg_in_in_ = mosi_sync_out;
	assign shreg_in_load_en = 1'b0;
	assign shreg_in_load_data = {nbits {1'b0}};
	assign shreg_out_clk = clk;
	assign shreg_out_reset = reset;
	assign shreg_out_in_ = 1'b0;
	assign shreg_out_load_en = pull_en;
	assign shreg_out_load_data = pull_msg;
	assign miso = shreg_out_out[nbits - 1];
	assign pull_en = cs_sync_negedge_;
	assign push_en = cs_sync_posedge_;
	assign push_msg = shreg_in_out;
	assign parity = ^push_msg[nbits - 3:0] & push_en;
	wire unused;
	assign unused = &{1'b0, mosi_sync_negedge_, mosi_sync_posedge_, sclk_sync_out, 1'b0};
endmodule
module spi_Minion (
	clk,
	reset,
	cs,
	sclk,
	mosi,
	miso,
	recv_msg,
	recv_rdy,
	recv_val,
	send_msg,
	send_rdy,
	send_val,
	minion_parity,
	adapter_parity
);
	parameter BIT_WIDTH = 32;
	parameter N_SAMPLES = 8;
	input wire clk;
	input wire reset;
	input wire cs;
	input wire sclk;
	input wire mosi;
	output wire miso;
	input wire [BIT_WIDTH - 1:0] recv_msg;
	output wire recv_rdy;
	input wire recv_val;
	output wire [BIT_WIDTH - 1:0] send_msg;
	input wire send_rdy;
	output wire send_val;
	output wire minion_parity;
	output wire adapter_parity;
	wire push_en;
	wire pull_en;
	wire [BIT_WIDTH + 1:0] push_msg;
	wire [BIT_WIDTH - 1:0] pull_msg;
	wire pull_msg_val;
	wire pull_msg_spc;
	spi_helpers_Minion_PushPull #(.nbits(BIT_WIDTH + 2)) minion(
		.clk(clk),
		.cs(cs),
		.miso(miso),
		.mosi(mosi),
		.reset(reset),
		.sclk(sclk),
		.pull_en(pull_en),
		.pull_msg({pull_msg_val, pull_msg_spc, pull_msg}),
		.push_en(push_en),
		.push_msg(push_msg),
		.parity(minion_parity)
	);
	spi_helpers_Minion_Adapter #(
		.nbits(BIT_WIDTH + 2),
		.num_entries(N_SAMPLES)
	) adapter1(
		.clk(clk),
		.reset(reset),
		.pull_en(pull_en),
		.pull_msg_val(pull_msg_val),
		.pull_msg_spc(pull_msg_spc),
		.pull_msg_data(pull_msg),
		.push_en(push_en),
		.push_msg_val_wrt(push_msg[BIT_WIDTH + 1]),
		.push_msg_val_rd(push_msg[BIT_WIDTH]),
		.push_msg_data(push_msg[BIT_WIDTH - 1:0]),
		.recv_msg(recv_msg),
		.recv_val(recv_val),
		.recv_rdy(recv_rdy),
		.send_msg(send_msg),
		.send_val(send_val),
		.send_rdy(send_rdy),
		.parity(adapter_parity)
	);
endmodule
module cmn_DemuxN (
	in,
	sel,
	out
);
	parameter nbits = 1;
	parameter noutputs = 2;
	input wire [nbits - 1:0] in;
	input wire [$clog2(noutputs) - 1:0] sel;
	output wire [(noutputs * nbits) - 1:0] out;
	genvar i;
	generate
		for (i = 0; i < noutputs; i = i + 1) begin : output_gen
			assign out[((noutputs - 1) - i) * nbits+:nbits] = (i == sel ? in : {nbits {1'b0}});
		end
	endgenerate
endmodule
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
`default_nettype none
module fft_helpers_SineWave (out);
	parameter signed [31:0] N = 8;
	parameter signed [31:0] W = 32;
	parameter signed [31:0] D = 16;
	output wire [(N * W) - 1:0] out;
	localparam real PI = $acos(-1);
	generate
		if (D >= 32) begin : genblk1
			$error("D must be less than 32");
		end
	endgenerate
	genvar i;
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	generate
		for (i = 0; i < N; i = i + 1) begin : genblk2
			localparam real sinvalue = $sin(((2 * PI) * i) / N);
			reg signed [31:0] fixedptvalue = sv2v_cast_32_signed(sinvalue * (2.0 ** D));
			assign out[((N - 1) - i) * W+:W] = {{(W - D) - 1 {fixedptvalue[31]}}, fixedptvalue[D:0]};
		end
	endgenerate
endmodule
`default_nettype none
module fft_helpers_BitReverse (
	in,
	out
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] in;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] out;
	localparam signed [31:0] n = $clog2(N_SAMPLES);
	generate
		if (N_SAMPLES == 8) begin : genblk1
			assign out[(N_SAMPLES - 1) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 1) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 2) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 5) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 3) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 3) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 4) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 7) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 5) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 2) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 6) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 6) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 7) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 4) * BIT_WIDTH+:BIT_WIDTH];
			assign out[(N_SAMPLES - 8) * BIT_WIDTH+:BIT_WIDTH] = in[(N_SAMPLES - 8) * BIT_WIDTH+:BIT_WIDTH];
		end
		else begin : genblk1
			genvar m;
			for (m = 0; m < N_SAMPLES; m = m + 1) begin : genblk1
				wire [n - 1:0] m_rev;
				genvar i;
				for (i = 0; i < n; i = i + 1) begin : genblk1
					assign m_rev[(n - i) - 1] = m[i];
				end
				assign out[((N_SAMPLES - 1) - m) * BIT_WIDTH+:BIT_WIDTH] = in[((N_SAMPLES - 1) - m_rev) * BIT_WIDTH+:BIT_WIDTH];
			end
		end
	endgenerate
endmodule
`default_nettype none
`default_nettype none
`default_nettype none
module fixed_point_combinational_Multiplier (
	a,
	b,
	c
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	parameter [0:0] sign = 1;
	input wire [n - 1:0] a;
	input wire [n - 1:0] b;
	output wire [n - 1:0] c;
	wire [(d + n) - 1:0] prod;
	wire [(d + n) - 1:0] a_ext;
	wire [(d + n) - 1:0] b_ext;
	generate
		if (sign) begin : genblk1
			assign a_ext = {{d {a[n - 1]}}, a};
			assign b_ext = {{d {b[n - 1]}}, b};
			assign prod = a_ext * b_ext;
		end
		else begin : genblk1
			assign prod = a * b;
		end
	endgenerate
	assign c = prod[(n + d) - 1:d];
	generate
		if (d > 0) begin : genblk2
			wire unused;
			assign unused = &{1'b0, prod[d - 1:0], 1'b0};
		end
	endgenerate
endmodule
module fixed_point_combinational_ComplexMultiplierS (
	ar,
	ac,
	br,
	bc,
	cr,
	cc
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	output wire [n - 1:0] cr;
	output wire [n - 1:0] cc;
	wire [n - 1:0] c_ar;
	wire [n - 1:0] c_ac;
	wire [n - 1:0] c_br;
	wire [n - 1:0] c_bc;
	wire [n - 1:0] arXbr;
	wire [n - 1:0] acXbc;
	wire [n - 1:0] arcXbrc;
	assign c_ar = ar;
	assign c_ac = ac;
	assign c_br = br;
	assign c_bc = bc;
	fixed_point_combinational_Multiplier #(
		.n(n),
		.d(d),
		.sign(1)
	) arXbrMult(
		.a(c_ar),
		.b(c_br),
		.c(arXbr)
	);
	fixed_point_combinational_Multiplier #(
		.n(n),
		.d(d),
		.sign(1)
	) acXbcMult(
		.a(c_ac),
		.b(c_bc),
		.c(acXbc)
	);
	fixed_point_combinational_Multiplier #(
		.n(n),
		.d(d),
		.sign(1)
	) arXbrcMult(
		.a(c_ar + c_ac),
		.b(c_br + c_bc),
		.c(arcXbrc)
	);
	assign cr = arXbr - acXbc;
	assign cc = (arcXbrc - arXbr) - acXbc;
endmodule
module fixed_point_combinational_ComplexMultiplier (
	clk,
	reset,
	recv_val,
	recv_rdy,
	send_val,
	send_rdy,
	ar,
	ac,
	br,
	bc,
	cr,
	cc
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	parameter signed [31:0] num_mults = 1;
	input wire clk;
	input wire reset;
	input wire recv_val;
	output reg recv_rdy;
	output reg send_val;
	input wire send_rdy;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	output wire [n - 1:0] cr;
	output wire [n - 1:0] cc;
	reg [n - 1:0] c_ar;
	reg [n - 1:0] c_ac;
	reg [n - 1:0] c_br;
	reg [n - 1:0] c_bc;
	reg [n - 1:0] arXbr;
	reg [n - 1:0] acXbc;
	reg [n - 1:0] arcXbrc;
	generate
		if (num_mults == 3) begin : genblk1
			wire [n:1] sv2v_tmp_1272E;
			assign sv2v_tmp_1272E = ar;
			always @(*) c_ar = sv2v_tmp_1272E;
			wire [n:1] sv2v_tmp_AE874;
			assign sv2v_tmp_AE874 = ac;
			always @(*) c_ac = sv2v_tmp_AE874;
			wire [n:1] sv2v_tmp_29444;
			assign sv2v_tmp_29444 = br;
			always @(*) c_br = sv2v_tmp_29444;
			wire [n:1] sv2v_tmp_F85B2;
			assign sv2v_tmp_F85B2 = bc;
			always @(*) c_bc = sv2v_tmp_F85B2;
			wire [n:1] sv2v_tmp_arXbrMult_c;
			always @(*) arXbr = sv2v_tmp_arXbrMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrMult(
				.a(c_ar),
				.b(c_br),
				.c(sv2v_tmp_arXbrMult_c)
			);
			wire [n:1] sv2v_tmp_acXbcMult_c;
			always @(*) acXbc = sv2v_tmp_acXbcMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) acXbcMult(
				.a(c_ac),
				.b(c_bc),
				.c(sv2v_tmp_acXbcMult_c)
			);
			wire [n:1] sv2v_tmp_arXbrcMult_c;
			always @(*) arcXbrc = sv2v_tmp_arXbrcMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrcMult(
				.a(c_ar + c_ac),
				.b(c_br + c_bc),
				.c(sv2v_tmp_arXbrcMult_c)
			);
			assign cr = arXbr - acXbc;
			assign cc = (arcXbrc - arXbr) - acXbc;
			wire [1:1] sv2v_tmp_1010E;
			assign sv2v_tmp_1010E = send_rdy;
			always @(*) recv_rdy = sv2v_tmp_1010E;
			wire [1:1] sv2v_tmp_3CA7E;
			assign sv2v_tmp_3CA7E = recv_val;
			always @(*) send_val = sv2v_tmp_3CA7E;
			reg unused = &{clk, reset};
		end
		else if (num_mults == 1) begin : genblk1
			reg [2:0] IDLE = 3'd0;
			reg [2:0] MUL1 = 3'd1;
			reg [2:0] MUL2 = 3'd2;
			reg [2:0] MUL3 = 3'd3;
			reg [2:0] DONE = 3'd4;
			reg [2:0] state;
			reg [2:0] next_state;
			reg [n - 1:0] mul_a;
			reg [n - 1:0] mul_b;
			wire [n - 1:0] mul_c;
			reg unused = &{IDLE, MUL1, MUL2, MUL3, DONE};
			always @(posedge clk)
				if (reset) begin
					state <= IDLE;
					c_ar <= 0;
					c_ac <= 0;
					c_br <= 0;
					c_bc <= 0;
					arXbr <= 0;
					acXbc <= 0;
					arcXbrc <= 0;
				end
				else begin
					state <= next_state;
					if ((state == IDLE) && recv_val) begin
						c_ar <= ar;
						c_ac <= ac;
						c_br <= br;
						c_bc <= bc;
						arXbr <= 0;
						acXbc <= 0;
						arcXbrc <= 0;
					end
					else if (state == MUL1)
						arXbr <= mul_c;
					else if (state == MUL2)
						acXbc <= mul_c;
					else if (state == MUL3)
						arcXbrc <= mul_c;
				end
			always @(*) begin
				next_state = state;
				recv_rdy = 0;
				send_val = 0;
				mul_a = 0;
				mul_b = 0;
				case (state)
					IDLE: begin
						recv_rdy = 1;
						if (recv_val)
							next_state = MUL1;
						else
							next_state = IDLE;
					end
					MUL1: begin
						next_state = MUL2;
						mul_a = c_ar;
						mul_b = c_br;
					end
					MUL2: begin
						next_state = MUL3;
						mul_a = c_ac;
						mul_b = c_bc;
					end
					MUL3: begin
						next_state = DONE;
						mul_a = c_ar + c_ac;
						mul_b = c_br + c_bc;
					end
					DONE: begin
						send_val = 1;
						if (send_rdy)
							next_state = IDLE;
						else
							next_state = state;
					end
					default:
						;
				endcase
			end
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrMult(
				.a(mul_a),
				.b(mul_b),
				.c(mul_c)
			);
			assign cr = arXbr - acXbc;
			assign cc = (arcXbrc - arXbr) - acXbc;
		end
	endgenerate
endmodule
module fixed_point_combinational_Butterfly (
	ar,
	ac,
	br,
	bc,
	wr,
	wc,
	cr,
	cc,
	dr,
	dc
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	parameter signed [31:0] b = 4;
	input wire [(b * n) - 1:0] ar;
	input wire [(b * n) - 1:0] ac;
	input wire [(b * n) - 1:0] br;
	input wire [(b * n) - 1:0] bc;
	input wire [(b * n) - 1:0] wr;
	input wire [(b * n) - 1:0] wc;
	output wire [(b * n) - 1:0] cr;
	output wire [(b * n) - 1:0] cc;
	output wire [(b * n) - 1:0] dr;
	output wire [(b * n) - 1:0] dc;
	wire [n - 1:0] m_cr [0:b - 1];
	wire [n - 1:0] m_cc [0:b - 1];
	genvar i;
	generate
		for (i = 0; i < b; i = i + 1) begin : genblk1
			fixed_point_combinational_ComplexMultiplierS #(
				.n(n),
				.d(d)
			) mult(
				.ar(wr[((b - 1) - i) * n+:n]),
				.ac(wc[((b - 1) - i) * n+:n]),
				.br(br[((b - 1) - i) * n+:n]),
				.bc(bc[((b - 1) - i) * n+:n]),
				.cr(m_cr[i]),
				.cc(m_cc[i])
			);
			assign cc[((b - 1) - i) * n+:n] = ac[((b - 1) - i) * n+:n] + m_cc[i];
			assign cr[((b - 1) - i) * n+:n] = ar[((b - 1) - i) * n+:n] + m_cr[i];
			assign dc[((b - 1) - i) * n+:n] = ac[((b - 1) - i) * n+:n] - m_cc[i];
			assign dr[((b - 1) - i) * n+:n] = ar[((b - 1) - i) * n+:n] - m_cr[i];
		end
	endgenerate
endmodule
module fft_pease_helpers_StridePermutation (
	recv,
	send
);
	parameter signed [31:0] N_SAMPLES = 8;
	parameter signed [31:0] BIT_WIDTH = 32;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send;
	genvar i;
	generate
		for (i = 0; i < (N_SAMPLES / 2); i = i + 1) begin : genblk1
			assign send[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = recv[((N_SAMPLES - 1) - (i * 2)) * BIT_WIDTH+:BIT_WIDTH];
			assign send[((N_SAMPLES - 1) - (i + (N_SAMPLES / 2))) * BIT_WIDTH+:BIT_WIDTH] = recv[((N_SAMPLES - 1) - ((i * 2) + 1)) * BIT_WIDTH+:BIT_WIDTH];
		end
	endgenerate
endmodule
module fft_pease_helpers_TwiddleGenerator (
	sine_wave_in,
	twiddle_real,
	twiddle_imaginary
);
	parameter signed [31:0] BIT_WIDTH = 4;
	parameter signed [31:0] DECIMAL_PT = 2;
	parameter signed [31:0] SIZE_FFT = 8;
	parameter signed [31:0] STAGE_FFT = 0;
	input wire [(SIZE_FFT * BIT_WIDTH) - 1:0] sine_wave_in;
	output wire [((SIZE_FFT / 2) * BIT_WIDTH) - 1:0] twiddle_real;
	output wire [((SIZE_FFT / 2) * BIT_WIDTH) - 1:0] twiddle_imaginary;
	generate
		if (STAGE_FFT == 0) begin : genblk1
			genvar i;
			for (i = 0; i < (SIZE_FFT / 2); i = i + 1) begin : genblk1
				assign twiddle_real[(((SIZE_FFT / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = {{(BIT_WIDTH - DECIMAL_PT) - 1 {1'b0}}, 1'b1, {DECIMAL_PT {1'b0}}};
				assign twiddle_imaginary[(((SIZE_FFT / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = 0;
			end
			wire [(BIT_WIDTH * SIZE_FFT) - 1:0] packed_sine_wave_in;
			function automatic [(BIT_WIDTH * SIZE_FFT) - 1:0] _sv2v_strm_FCE0D;
				input reg [(0 + (SIZE_FFT * BIT_WIDTH)) - 1:0] inp;
				reg [(0 + (SIZE_FFT * BIT_WIDTH)) - 1:0] _sv2v_strm_3A5FA_inp;
				reg [(0 + (SIZE_FFT * BIT_WIDTH)) - 1:0] _sv2v_strm_3A5FA_out;
				integer _sv2v_strm_3A5FA_idx;
				begin
					_sv2v_strm_3A5FA_inp = {inp};
					for (_sv2v_strm_3A5FA_idx = 0; _sv2v_strm_3A5FA_idx <= ((0 + (SIZE_FFT * BIT_WIDTH)) - SIZE_FFT); _sv2v_strm_3A5FA_idx = _sv2v_strm_3A5FA_idx + SIZE_FFT)
						_sv2v_strm_3A5FA_out[((0 + (SIZE_FFT * BIT_WIDTH)) - 1) - _sv2v_strm_3A5FA_idx-:SIZE_FFT] = _sv2v_strm_3A5FA_inp[_sv2v_strm_3A5FA_idx+:SIZE_FFT];
					if (((0 + (SIZE_FFT * BIT_WIDTH)) % SIZE_FFT) > 0)
						_sv2v_strm_3A5FA_out[0+:(0 + (SIZE_FFT * BIT_WIDTH)) % SIZE_FFT] = _sv2v_strm_3A5FA_inp[_sv2v_strm_3A5FA_idx+:(0 + (SIZE_FFT * BIT_WIDTH)) % SIZE_FFT];
					_sv2v_strm_FCE0D = ((0 + (SIZE_FFT * BIT_WIDTH)) <= (BIT_WIDTH * SIZE_FFT) ? _sv2v_strm_3A5FA_out << ((BIT_WIDTH * SIZE_FFT) - (0 + (SIZE_FFT * BIT_WIDTH))) : _sv2v_strm_3A5FA_out >> ((0 + (SIZE_FFT * BIT_WIDTH)) - (BIT_WIDTH * SIZE_FFT)));
				end
			endfunction
			assign packed_sine_wave_in = _sv2v_strm_FCE0D({sine_wave_in});
			reg unused = &packed_sine_wave_in;
		end
		else begin : genblk1
			genvar m;
			for (m = 0; m < (2 ** STAGE_FFT); m = m + 1) begin : genblk1
				genvar j;
				for (j = 0; j < (2 ** (($clog2(SIZE_FFT) - STAGE_FFT) - 1)); j = j + 1) begin : genblk1
					localparam signed [31:0] stageLeft = ($clog2(SIZE_FFT) - STAGE_FFT) - 1;
					localparam signed [31:0] idx = m * (2 ** stageLeft);
					localparam signed [31:0] si = idx + j;
					assign twiddle_real[(((SIZE_FFT / 2) - 1) - si) * BIT_WIDTH+:BIT_WIDTH] = sine_wave_in[((SIZE_FFT - 1) - (idx + (SIZE_FFT / 4))) * BIT_WIDTH+:BIT_WIDTH];
					assign twiddle_imaginary[(((SIZE_FFT / 2) - 1) - si) * BIT_WIDTH+:BIT_WIDTH] = sine_wave_in[((SIZE_FFT - 1) - (idx + (SIZE_FFT / 2))) * BIT_WIDTH+:BIT_WIDTH];
				end
			end
		end
	endgenerate
endmodule
module fft_pease_FFT (
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
	parameter signed [31:0] DECIMAL_PT = 16;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg;
	input wire recv_val;
	output wire recv_rdy;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg;
	output wire send_val;
	input wire send_rdy;
	input wire reset;
	input wire clk;
	reg [2:0] IDLE = 3'd0;
	reg [2:0] COMP = 3'd1;
	reg [2:0] DONE = 3'd2;
	localparam signed [31:0] BstageBits = (N_SAMPLES > 2 ? $clog2($clog2(N_SAMPLES)) : 1);
	localparam signed [31:0] log = $clog2(N_SAMPLES) - 1;
	reg [BstageBits - 1:0] max_bstage = log[BstageBits - 1:0];
	reg [2:0] state;
	reg [2:0] next_state;
	assign recv_rdy = (state == IDLE) || (state == DONE);
	assign send_val = state == DONE;
	reg [BstageBits - 1:0] bstage;
	reg [BstageBits - 1:0] next_bstage;
	wire [(N_SAMPLES * (2 * BIT_WIDTH)) - 1:0] out_stride;
	reg [(2 * BIT_WIDTH) - 1:0] in_butterfly [0:N_SAMPLES - 1];
	wire [(N_SAMPLES * (2 * BIT_WIDTH)) - 1:0] out_butterfly;
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] reversed_msg;
	fft_helpers_BitReverse #(
		.N_SAMPLES(N_SAMPLES),
		.BIT_WIDTH(BIT_WIDTH)
	) bit_reverse(
		.in(recv_msg),
		.out(reversed_msg)
	);
	fft_pease_helpers_StridePermutation #(
		.N_SAMPLES(N_SAMPLES),
		.BIT_WIDTH(BIT_WIDTH * 2)
	) stride_permutation(
		.recv(out_butterfly),
		.send(out_stride)
	);
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] sine_wave_out;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] wr [0:$clog2(N_SAMPLES) - 1];
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] wc [0:$clog2(N_SAMPLES) - 1];
	genvar i;
	generate
		for (i = 0; i < $clog2(N_SAMPLES); i = i + 1) begin : genblk1
			fft_pease_helpers_TwiddleGenerator #(
				.BIT_WIDTH(BIT_WIDTH),
				.DECIMAL_PT(DECIMAL_PT),
				.SIZE_FFT(N_SAMPLES),
				.STAGE_FFT(i)
			) twiddle_generator(
				.sine_wave_in(sine_wave_out),
				.twiddle_real(wr[i]),
				.twiddle_imaginary(wc[i])
			);
		end
	endgenerate
	fft_helpers_SineWave #(
		.N(N_SAMPLES),
		.W(BIT_WIDTH),
		.D(DECIMAL_PT)
	) sine_wave(.out(sine_wave_out));
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] ar;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] ac;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] br;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] bc;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] cr;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] cc;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] dr;
	wire [((N_SAMPLES / 2) * BIT_WIDTH) - 1:0] dc;
	generate
		for (i = 0; i < (N_SAMPLES / 2); i = i + 1) begin : genblk2
			assign ar[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[i * 2][BIT_WIDTH - 1:0];
			assign ac[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[i * 2][(2 * BIT_WIDTH) - 1:BIT_WIDTH];
			assign br[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[(i * 2) + 1][BIT_WIDTH - 1:0];
			assign bc[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[(i * 2) + 1][(2 * BIT_WIDTH) - 1:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - (i * 2)) * (2 * BIT_WIDTH)) + (BIT_WIDTH - 1)-:BIT_WIDTH] = cr[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - (i * 2)) * (2 * BIT_WIDTH)) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (2 * BIT_WIDTH) - 1 : (((2 * BIT_WIDTH) - 1) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)) - 1)-:(((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)] = cc[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - ((i * 2) + 1)) * (2 * BIT_WIDTH)) + (BIT_WIDTH - 1)-:BIT_WIDTH] = dr[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
			assign out_butterfly[(((N_SAMPLES - 1) - ((i * 2) + 1)) * (2 * BIT_WIDTH)) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (2 * BIT_WIDTH) - 1 : (((2 * BIT_WIDTH) - 1) + (((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)) - 1)-:(((2 * BIT_WIDTH) - 1) >= BIT_WIDTH ? (((2 * BIT_WIDTH) - 1) - BIT_WIDTH) + 1 : (BIT_WIDTH - ((2 * BIT_WIDTH) - 1)) + 1)] = dc[(((N_SAMPLES / 2) - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
		end
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk3
			assign send_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = in_butterfly[i][BIT_WIDTH - 1:0];
		end
	endgenerate
	fixed_point_combinational_Butterfly #(
		.n(BIT_WIDTH),
		.d(DECIMAL_PT),
		.b(N_SAMPLES / 2)
	) fft_stage(
		.wr(wr[bstage]),
		.wc(wc[bstage]),
		.ar(ar),
		.ac(ac),
		.br(br),
		.bc(bc),
		.cr(cr),
		.cc(cc),
		.dr(dr),
		.dc(dc)
	);
	always @(*) begin
		next_state = state;
		next_bstage = bstage;
		if ((state == IDLE) && recv_val)
			next_state = COMP;
		else if (state == COMP) begin
			if (bstage == max_bstage) begin
				next_state = DONE;
				next_bstage = 0;
			end
			else
				next_bstage = bstage + 1;
		end
		else if ((state == DONE) && send_rdy)
			if (recv_val)
				next_state = COMP;
			else
				next_state = IDLE;
	end
	always @(posedge clk)
		if (reset) begin
			state <= IDLE;
			bstage <= 0;
		end
		else begin
			state <= next_state;
			bstage <= next_bstage;
		end
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk4
			always @(posedge clk)
				if (reset)
					in_butterfly[i] <= 0;
				else if ((state == IDLE) || ((state == DONE) && recv_val)) begin
					in_butterfly[i][BIT_WIDTH - 1:0] <= reversed_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH];
					in_butterfly[i][(2 * BIT_WIDTH) - 1:BIT_WIDTH] <= 0;
				end
				else if (state == COMP)
					in_butterfly[i] <= out_stride[((N_SAMPLES - 1) - i) * (2 * BIT_WIDTH)+:2 * BIT_WIDTH];
		end
	endgenerate
endmodule
`default_nettype none
module serdes_Deserializer (
	recv_val,
	recv_rdy,
	recv_msg,
	send_val,
	send_rdy,
	send_msg,
	clk,
	reset
);
	parameter signed [31:0] N_SAMPLES = 8;
	parameter signed [31:0] BIT_WIDTH = 32;
	input wire recv_val;
	output wire recv_rdy;
	input wire [BIT_WIDTH - 1:0] recv_msg;
	output wire send_val;
	input wire send_rdy;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg;
	input wire clk;
	input wire reset;
	generate
		if (N_SAMPLES == 1) begin : genblk1
			assign recv_rdy = send_rdy;
			assign send_val = recv_val;
			assign send_msg[(N_SAMPLES - 1) * BIT_WIDTH+:BIT_WIDTH] = recv_msg;
			reg unused = {1'b0, clk, reset, 1'b0};
		end
		else begin : genblk1
			wire [N_SAMPLES - 1:0] en_sel;
			DeserializerControl #(.N_SAMPLES(N_SAMPLES)) c(
				.recv_val(recv_val),
				.send_rdy(send_rdy),
				.send_val(send_val),
				.recv_rdy(recv_rdy),
				.reset(reset),
				.clk(clk),
				.en_sel(en_sel)
			);
			genvar i;
			for (i = 0; i < N_SAMPLES; i = i + 1) begin : l_regs
				cmn_EnResetReg #(.p_nbits(BIT_WIDTH)) register(
					.clk(clk),
					.reset(reset),
					.en(recv_rdy & en_sel[i]),
					.d(recv_msg),
					.q(send_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH])
				);
			end
		end
	endgenerate
endmodule
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
module Decoder (
	in,
	out
);
	parameter signed [31:0] BIT_WIDTH = 3;
	input wire [BIT_WIDTH - 1:0] in;
	output wire [(1 << BIT_WIDTH) - 1:0] out;
	assign out = {{(1 << BIT_WIDTH) - 1 {1'b0}}, 1'b1} << in;
endmodule
`default_nettype none
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
`default_nettype none
`default_nettype none
module magnitude_Magnitude (
	recv_msg,
	send_msg
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire signed [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] send_msg;
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign send_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = (recv_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] < 0 ? -recv_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] : recv_msg[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH]);
		end
	endgenerate
endmodule
`default_nettype none
module highpass_Highpass (
	cutoff_freq,
	freq_in,
	filtered_valid
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [BIT_WIDTH - 1:0] cutoff_freq;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] freq_in;
	output wire [0:N_SAMPLES - 1] filtered_valid;
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign filtered_valid[i] = freq_in[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] > cutoff_freq;
		end
	endgenerate
endmodule
`default_nettype none
module classifier_helpers_FrequencyBins (
	sampling_freq,
	frequency_out
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 16;
	input wire [BIT_WIDTH - 1:0] sampling_freq;
	output wire [(N_SAMPLES * BIT_WIDTH) - 1:0] frequency_out;
	localparam signed [31:0] LOG2_N_SAMPLES = $clog2(N_SAMPLES);
	initial if ($pow(2, LOG2_N_SAMPLES) != N_SAMPLES)
		$error("N_SAMPLES must be a power of 2");
	function automatic signed [LOG2_N_SAMPLES - 1:0] sv2v_cast_B215B_signed;
		input reg signed [LOG2_N_SAMPLES - 1:0] inp;
		sv2v_cast_B215B_signed = inp;
	endfunction
	wire [(LOG2_N_SAMPLES + BIT_WIDTH) - 1:0] wide_sampling_freq = {sv2v_cast_B215B_signed(0), sampling_freq};
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : gen_freq
			wire [(LOG2_N_SAMPLES + BIT_WIDTH) - 1:0] wide_freq_out = (i * wide_sampling_freq) >> (LOG2_N_SAMPLES + 1);
			assign frequency_out[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] = wide_freq_out[BIT_WIDTH - 1:0];
			wire unused = &{1'b0, wide_freq_out[(LOG2_N_SAMPLES + BIT_WIDTH) - 1:BIT_WIDTH], 1'b0};
		end
	endgenerate
endmodule
`default_nettype none
module comparison_Comparison (
	cutoff_mag,
	filtered_valid,
	mag_in,
	compare_out
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire [BIT_WIDTH - 1:0] cutoff_mag;
	input wire [0:N_SAMPLES - 1] filtered_valid;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] mag_in;
	output wire compare_out;
	wire [N_SAMPLES - 1:0] compare_outs;
	genvar i;
	generate
		for (i = 0; i < N_SAMPLES; i = i + 1) begin : genblk1
			assign compare_outs[i] = filtered_valid[i] & (mag_in[((N_SAMPLES - 1) - i) * BIT_WIDTH+:BIT_WIDTH] > cutoff_mag);
		end
	endgenerate
	assign compare_out = compare_outs != 0;
endmodule
module classifier_Classifier (
	clk,
	reset,
	recv_rdy,
	recv_val,
	recv_msg,
	cutoff_freq_rdy,
	cutoff_freq_val,
	cutoff_freq_msg,
	cutoff_mag_rdy,
	cutoff_mag_val,
	cutoff_mag_msg,
	sampling_freq_rdy,
	sampling_freq_val,
	sampling_freq_msg,
	send_rdy,
	send_val,
	send_msg
);
	parameter signed [31:0] BIT_WIDTH = 32;
	parameter signed [31:0] DECIMAL_PT = 16;
	parameter signed [31:0] FREQ_BIT_WIDTH = 16;
	parameter signed [31:0] N_SAMPLES = 8;
	input wire clk;
	input wire reset;
	output wire recv_rdy;
	input wire recv_val;
	input wire [(N_SAMPLES * BIT_WIDTH) - 1:0] recv_msg;
	output wire cutoff_freq_rdy;
	input wire cutoff_freq_val;
	input wire [FREQ_BIT_WIDTH - 1:0] cutoff_freq_msg;
	output wire cutoff_mag_rdy;
	input wire cutoff_mag_val;
	input wire [BIT_WIDTH - 1:0] cutoff_mag_msg;
	output wire sampling_freq_rdy;
	input wire sampling_freq_val;
	input wire [FREQ_BIT_WIDTH - 1:0] sampling_freq_msg;
	input wire send_rdy;
	output wire send_val;
	output wire send_msg;
	wire [FREQ_BIT_WIDTH - 1:0] in_cutoff_freq;
	wire [BIT_WIDTH - 1:0] in_cutoff_mag;
	wire [FREQ_BIT_WIDTH - 1:0] in_sampling_freq;
	cmn_EnResetReg #(
		.p_nbits(FREQ_BIT_WIDTH),
		.p_reset_value(0)
	) cutoff_freq_in(
		.clk(clk),
		.reset(reset),
		.d(cutoff_freq_msg),
		.q(in_cutoff_freq),
		.en(cutoff_freq_val)
	);
	assign cutoff_freq_rdy = 1;
	cmn_EnResetReg #(
		.p_nbits(BIT_WIDTH),
		.p_reset_value(0)
	) cutoff_mag_in(
		.clk(clk),
		.reset(reset),
		.d(cutoff_mag_msg),
		.q(in_cutoff_mag),
		.en(cutoff_mag_val)
	);
	assign cutoff_mag_rdy = 1;
	cmn_EnResetReg #(
		.p_nbits(FREQ_BIT_WIDTH),
		.p_reset_value(0)
	) sampling_freq_in(
		.clk(clk),
		.reset(reset),
		.d(sampling_freq_msg),
		.q(in_sampling_freq),
		.en(sampling_freq_val)
	);
	assign sampling_freq_rdy = 1;
	wire [(N_SAMPLES * BIT_WIDTH) - 1:0] out_mag;
	magnitude_Magnitude #(
		.BIT_WIDTH(BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) mag_calc(
		.recv_msg(recv_msg),
		.send_msg(out_mag)
	);
	wire [(N_SAMPLES * FREQ_BIT_WIDTH) - 1:0] frequency_array;
	classifier_helpers_FrequencyBins #(
		.BIT_WIDTH(FREQ_BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) freq_gen(
		.sampling_freq(in_sampling_freq),
		.frequency_out(frequency_array)
	);
	wire [0:N_SAMPLES - 1] out_filter;
	highpass_Highpass #(
		.BIT_WIDTH(FREQ_BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) highpass_fil(
		.cutoff_freq(in_cutoff_freq),
		.freq_in(frequency_array),
		.filtered_valid(out_filter)
	);
	wire out_comparison;
	comparison_Comparison #(
		.BIT_WIDTH(BIT_WIDTH),
		.N_SAMPLES(N_SAMPLES)
	) comparison(
		.cutoff_mag(in_cutoff_mag),
		.filtered_valid(out_filter),
		.mag_in(out_mag),
		.compare_out(out_comparison)
	);
	assign send_msg = out_comparison;
	assign send_val = recv_val;
	assign recv_rdy = send_rdy;
endmodule
module lbist_controller (
	clk,
	reset,
	lbist_req_val,
	lbist_req_rdy,
	lbist_resp_val,
	lbist_resp_msg,
	lbist_resp_rdy,
	lfsr_resp_val,
	lfsr_resp_msg,
	lfsr_resp_rdy,
	misr_req_val,
	misr_req_msg,
	misr_req_rdy,
	misr_resp_val,
	misr_resp_msg,
	misr_resp_rdy,
	lfsr_cut_reset
);
	parameter signed [31:0] SEED_BITS = 32;
	parameter signed [31:0] SIGNATURE_BITS = 32;
	parameter signed [31:0] NUM_SEEDS = 8;
	parameter signed [31:0] NUM_HASHES = 8;
	parameter signed [31:0] MAX_OUTPUTS_TO_HASH = 32;
	parameter signed [31:0] MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH);
	parameter [(NUM_SEEDS * SEED_BITS) - 1:0] LFSR_SEEDS = 256'h0a89687ea87ded5f481c507781595729ffd3976924b05d579913b1fdd8df8ed2;
	parameter [(NUM_SEEDS * SIGNATURE_BITS) - 1:0] EXPECTED_SIGNATURES = 256'h2435b217b25e4d4c16307bd12ced25e0c5145ccb6180254bc329c75c89b9c2ec;
	input wire clk;
	input wire reset;
	input wire lbist_req_val;
	output reg lbist_req_rdy;
	output reg lbist_resp_val;
	output reg [NUM_SEEDS - 1:0] lbist_resp_msg;
	input wire lbist_resp_rdy;
	output reg lfsr_resp_val;
	output reg [SEED_BITS - 1:0] lfsr_resp_msg;
	input wire lfsr_resp_rdy;
	output reg misr_req_val;
	output reg [MISR_MSG_BITS:0] misr_req_msg;
	input wire misr_req_rdy;
	input wire misr_resp_val;
	input wire [SIGNATURE_BITS - 1:0] misr_resp_msg;
	output reg misr_resp_rdy;
	output reg lfsr_cut_reset;
	localparam [1:0] IDLE = 2'd0;
	localparam [1:0] START = 2'd1;
	localparam [1:0] COMP_SIG = 2'd2;
	reg [1:0] state;
	reg [1:0] next_state;
	reg [$clog2(NUM_SEEDS) - 1:0] counter;
	always @(*)
		case (state)
			IDLE: begin
				lbist_req_rdy = 1;
				lfsr_resp_val = 0;
				lfsr_resp_msg = 0;
				misr_req_val = 0;
				misr_req_msg = 0;
				misr_resp_rdy = 0;
				lfsr_cut_reset = 0;
			end
			START: begin
				lbist_req_rdy = 0;
				lfsr_resp_val = 1;
				lfsr_resp_msg = LFSR_SEEDS[counter * SEED_BITS+:SEED_BITS];
				misr_req_val = 1;
				misr_req_msg = NUM_HASHES;
				misr_resp_rdy = 0;
				lfsr_cut_reset = 0;
			end
			COMP_SIG: begin
				lbist_req_rdy = 0;
				lfsr_resp_val = 0;
				lfsr_resp_msg = 0;
				misr_req_val = 0;
				misr_req_msg = 0;
				misr_resp_rdy = 1;
				lfsr_cut_reset = 1;
			end
			default: begin
				lbist_req_rdy = 1;
				lfsr_resp_val = 0;
				lfsr_resp_msg = 0;
				misr_req_val = 0;
				misr_req_msg = 0;
				misr_resp_rdy = 0;
				lfsr_cut_reset = 0;
			end
		endcase
	always @(*)
		case (state)
			IDLE:
				if ((lbist_req_val && lfsr_resp_rdy) && misr_req_rdy)
					next_state = START;
				else
					next_state = IDLE;
			START:
				if (misr_resp_val)
					next_state = COMP_SIG;
				else
					next_state = START;
			COMP_SIG:
				if (counter != (NUM_SEEDS - 1))
					next_state = START;
				else if (lbist_resp_rdy && lbist_resp_val)
					next_state = IDLE;
				else
					next_state = COMP_SIG;
			default: next_state = IDLE;
		endcase
	always @(posedge clk)
		if (reset)
			state <= IDLE;
		else
			state <= next_state;
	always @(posedge clk)
		if (reset || (state == IDLE))
			counter <= 0;
		else if ((state == COMP_SIG) && (next_state == START))
			counter <= counter + 1;
		else
			counter <= counter;
	always @(posedge clk)
		case (state)
			IDLE: begin
				lbist_resp_val <= 0;
				lbist_resp_msg <= 1'sb0;
			end
			START: begin
				lbist_resp_val <= 0;
				lbist_resp_msg <= lbist_resp_msg;
			end
			COMP_SIG: begin
				lbist_resp_val <= counter == (NUM_SEEDS - 1);
				begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < NUM_SEEDS; i = i + 1)
						if ((i == counter) && misr_resp_val)
							lbist_resp_msg[i] <= misr_resp_msg == EXPECTED_SIGNATURES[i * SIGNATURE_BITS+:SIGNATURE_BITS];
						else
							lbist_resp_msg[i] <= lbist_resp_msg[i];
				end
			end
			default: begin
				lbist_resp_val <= 0;
				lbist_resp_msg <= 1'sb0;
			end
		endcase
endmodule
module lfsr_galois (
	clk,
	reset,
	req_msg,
	req_val,
	req_rdy,
	resp_rdy,
	resp_val,
	resp_msg
);
	parameter LFSR_MSG_BITS = 64;
	input wire clk;
	input wire reset;
	input wire [LFSR_MSG_BITS - 1:0] req_msg;
	input wire req_val;
	output reg req_rdy;
	input wire resp_rdy;
	output reg resp_val;
	output reg [LFSR_MSG_BITS - 1:0] resp_msg;
	reg [1:0] IDLE = 2'b00;
	reg [1:0] GEN_VAL = 2'b01;
	reg [1:0] state;
	reg [1:0] next_state;
	wire tap1;
	wire tap2;
	wire final_tap;
	reg [LFSR_MSG_BITS - 1:0] Q;
	wire [LFSR_MSG_BITS - 1:0] next_Q;
	wire signed [31:0] T1;
	wire signed [31:0] T2;
	wire signed [31:0] T3;
	wire signed [31:0] T4;
	localparam signed [31:0] NUM_TAPS = ((((((((((((((((((((((((((((((LFSR_MSG_BITS == 8) || (LFSR_MSG_BITS == 12)) || (LFSR_MSG_BITS == 13)) || (LFSR_MSG_BITS == 14)) || (LFSR_MSG_BITS == 16)) || (LFSR_MSG_BITS == 19)) || (LFSR_MSG_BITS == 24)) || (LFSR_MSG_BITS == 26)) || (LFSR_MSG_BITS == 27)) || (LFSR_MSG_BITS == 30)) || (LFSR_MSG_BITS == 32)) || (LFSR_MSG_BITS == 34)) || (LFSR_MSG_BITS == 37)) || (LFSR_MSG_BITS == 38)) || (LFSR_MSG_BITS == 40)) || (LFSR_MSG_BITS == 42)) || (LFSR_MSG_BITS == 43)) || (LFSR_MSG_BITS == 44)) || (LFSR_MSG_BITS == 45)) || (LFSR_MSG_BITS == 46)) || (LFSR_MSG_BITS == 48)) || (LFSR_MSG_BITS == 50)) || (LFSR_MSG_BITS == 51)) || (LFSR_MSG_BITS == 53)) || (LFSR_MSG_BITS == 54)) || (LFSR_MSG_BITS == 56)) || (LFSR_MSG_BITS == 59)) || (LFSR_MSG_BITS == 61)) || (LFSR_MSG_BITS == 62)) || (LFSR_MSG_BITS == 64) ? 1 : 0);
	generate
		if (LFSR_MSG_BITS == 2) begin : genblk1
			assign T1 = 0;
			assign T2 = 1;
		end
		else if (LFSR_MSG_BITS == 3) begin : genblk1
			assign T1 = 1;
			assign T2 = 2;
		end
		else if (LFSR_MSG_BITS == 4) begin : genblk1
			assign T1 = 2;
			assign T2 = 3;
		end
		else if (LFSR_MSG_BITS == 5) begin : genblk1
			assign T1 = 2;
			assign T2 = 4;
		end
		else if (LFSR_MSG_BITS == 6) begin : genblk1
			assign T1 = 4;
			assign T2 = 5;
		end
		else if (LFSR_MSG_BITS == 7) begin : genblk1
			assign T1 = 5;
			assign T2 = 6;
		end
		else if (LFSR_MSG_BITS == 8) begin : genblk1
			assign T1 = 3;
			assign T2 = 4;
			assign T3 = 5;
			assign T4 = 7;
		end
		else if (LFSR_MSG_BITS == 9) begin : genblk1
			assign T1 = 4;
			assign T2 = 8;
		end
		else if (LFSR_MSG_BITS == 10) begin : genblk1
			assign T1 = 6;
			assign T2 = 9;
		end
		else if (LFSR_MSG_BITS == 11) begin : genblk1
			assign T1 = 8;
			assign T2 = 10;
		end
		else if (LFSR_MSG_BITS == 12) begin : genblk1
			assign T1 = 5;
			assign T2 = 7;
			assign T3 = 10;
			assign T4 = 11;
		end
		else if (LFSR_MSG_BITS == 13) begin : genblk1
			assign T1 = 8;
			assign T2 = 9;
			assign T3 = 11;
			assign T4 = 12;
		end
		else if (LFSR_MSG_BITS == 14) begin : genblk1
			assign T1 = 8;
			assign T2 = 10;
			assign T3 = 12;
			assign T4 = 13;
		end
		else if (LFSR_MSG_BITS == 15) begin : genblk1
			assign T1 = 13;
			assign T2 = 14;
		end
		else if (LFSR_MSG_BITS == 16) begin : genblk1
			assign T1 = 10;
			assign T2 = 12;
			assign T3 = 13;
			assign T4 = 15;
		end
		else if (LFSR_MSG_BITS == 17) begin : genblk1
			assign T1 = 13;
			assign T2 = 16;
		end
		else if (LFSR_MSG_BITS == 18) begin : genblk1
			assign T1 = 10;
			assign T2 = 17;
		end
		else if (LFSR_MSG_BITS == 19) begin : genblk1
			assign T1 = 13;
			assign T2 = 16;
			assign T3 = 17;
			assign T4 = 18;
		end
		else if (LFSR_MSG_BITS == 20) begin : genblk1
			assign T1 = 16;
			assign T2 = 19;
		end
		else if (LFSR_MSG_BITS == 21) begin : genblk1
			assign T1 = 18;
			assign T2 = 20;
		end
		else if (LFSR_MSG_BITS == 22) begin : genblk1
			assign T1 = 20;
			assign T2 = 21;
		end
		else if (LFSR_MSG_BITS == 23) begin : genblk1
			assign T1 = 17;
			assign T2 = 22;
		end
		else if (LFSR_MSG_BITS == 24) begin : genblk1
			assign T1 = 19;
			assign T2 = 20;
			assign T3 = 22;
			assign T4 = 23;
		end
		else if (LFSR_MSG_BITS == 25) begin : genblk1
			assign T1 = 21;
			assign T2 = 24;
		end
		else if (LFSR_MSG_BITS == 26) begin : genblk1
			assign T1 = 19;
			assign T2 = 20;
			assign T3 = 24;
			assign T4 = 25;
		end
		else if (LFSR_MSG_BITS == 27) begin : genblk1
			assign T1 = 21;
			assign T2 = 22;
			assign T3 = 24;
			assign T4 = 26;
		end
		else if (LFSR_MSG_BITS == 28) begin : genblk1
			assign T1 = 24;
			assign T2 = 27;
		end
		else if (LFSR_MSG_BITS == 29) begin : genblk1
			assign T1 = 26;
			assign T2 = 28;
		end
		else if (LFSR_MSG_BITS == 30) begin : genblk1
			assign T1 = 23;
			assign T2 = 25;
			assign T3 = 27;
			assign T4 = 29;
		end
		else if (LFSR_MSG_BITS == 31) begin : genblk1
			assign T1 = 27;
			assign T2 = 30;
		end
		else if (LFSR_MSG_BITS == 32) begin : genblk1
			assign T1 = 24;
			assign T2 = 25;
			assign T3 = 29;
			assign T4 = 31;
		end
		else if (LFSR_MSG_BITS == 33) begin : genblk1
			assign T1 = 18;
			assign T2 = 32;
		end
		else if (LFSR_MSG_BITS == 34) begin : genblk1
			assign T1 = 24;
			assign T2 = 28;
			assign T3 = 29;
			assign T4 = 33;
		end
		else if (LFSR_MSG_BITS == 35) begin : genblk1
			assign T1 = 32;
			assign T2 = 34;
		end
		else if (LFSR_MSG_BITS == 36) begin : genblk1
			assign T1 = 25;
			assign T2 = 35;
		end
		else if (LFSR_MSG_BITS == 37) begin : genblk1
			assign T1 = 30;
			assign T2 = 32;
			assign T3 = 33;
			assign T4 = 36;
		end
		else if (LFSR_MSG_BITS == 38) begin : genblk1
			assign T1 = 31;
			assign T2 = 34;
			assign T3 = 36;
			assign T4 = 37;
		end
		else if (LFSR_MSG_BITS == 39) begin : genblk1
			assign T1 = 34;
			assign T2 = 38;
		end
		else if (LFSR_MSG_BITS == 40) begin : genblk1
			assign T1 = 35;
			assign T2 = 37;
			assign T3 = 38;
			assign T4 = 39;
		end
		else if (LFSR_MSG_BITS == 41) begin : genblk1
			assign T1 = 37;
			assign T2 = 40;
		end
		else if (LFSR_MSG_BITS == 42) begin : genblk1
			assign T1 = 38;
			assign T2 = 41;
		end
		else if (LFSR_MSG_BITS == 43) begin : genblk1
			assign T1 = 40;
			assign T2 = 42;
		end
		else if (LFSR_MSG_BITS == 44) begin : genblk1
			assign T1 = 39;
			assign T2 = 43;
		end
		else if (LFSR_MSG_BITS == 64) begin : genblk1
			assign T1 = 59;
			assign T2 = 60;
			assign T3 = 62;
			assign T4 = 63;
		end
		else begin : genblk1
			initial $fatal("Unsupported LFSR_MSG_BITS value: %d", LFSR_MSG_BITS);
		end
		if (NUM_TAPS == 1'b1) begin : genblk2
			assign final_tap = ~(((Q[T2] ^ Q[T3]) ^ Q[T4]) ^ Q[T1]);
		end
		else if (NUM_TAPS == 1'b0) begin : genblk2
			assign final_tap = Q[T2] ^ Q[T1];
		end
		else begin : genblk2
			initial $fatal("Unsupported NUM_TAPS value: %d", NUM_TAPS);
		end
	endgenerate
	assign next_Q = {Q[LFSR_MSG_BITS - 2:0], final_tap};
	always @(posedge clk) begin
		if (reset) begin
			state <= IDLE;
			Q <= 1'sb0;
		end
		else if (state == IDLE)
			Q <= req_msg;
		else if (state == GEN_VAL) begin
			if (resp_rdy)
				Q <= next_Q;
		end
		else
			Q <= Q;
		state <= next_state;
	end
	always @(*)
		case (state)
			IDLE:
				if (reset)
					next_state = IDLE;
				else if (req_val)
					next_state = GEN_VAL;
				else
					next_state = IDLE;
			GEN_VAL:
				if (reset)
					next_state = IDLE;
				else
					next_state = GEN_VAL;
			default: next_state = IDLE;
		endcase
	always @(*)
		case (state)
			IDLE: begin
				req_rdy = 1'b1;
				resp_val = 1'b0;
				resp_msg = 1'sb0;
			end
			GEN_VAL: begin
				req_rdy = 1'b0;
				resp_val = 1'b1;
				resp_msg = Q;
			end
			default: begin
				req_rdy = 1'b0;
				resp_val = 1'b0;
				resp_msg = 1'sb0;
			end
		endcase
endmodule
module misr (
	clk,
	reset,
	cut_req_val,
	cut_req_msg,
	cut_req_rdy,
	lbist_req_val,
	lbist_req_msg,
	lbist_req_rdy,
	lbist_resp_val,
	lbist_resp_msg,
	lbist_resp_rdy
);
	parameter signed [31:0] CUT_MSG_BITS = 32;
	parameter signed [31:0] SIGNATURE_BITS = 32;
	parameter signed [31:0] MAX_OUTPUTS_TO_HASH = 32;
	parameter signed [31:0] SEED = 32'd0;
	parameter signed [31:0] LBIST_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH);
	input wire clk;
	input wire reset;
	input wire cut_req_val;
	input wire [CUT_MSG_BITS - 1:0] cut_req_msg;
	output reg cut_req_rdy;
	input wire lbist_req_val;
	input wire [LBIST_MSG_BITS:0] lbist_req_msg;
	output reg lbist_req_rdy;
	output reg lbist_resp_val;
	output reg [SIGNATURE_BITS - 1:0] lbist_resp_msg;
	input wire lbist_resp_rdy;
	reg [1:0] state;
	reg [1:0] next_state;
	wire [$clog2(MAX_OUTPUTS_TO_HASH):0] next_outputs_hashed;
	reg [$clog2(MAX_OUTPUTS_TO_HASH):0] outputs_hashed;
	reg [$clog2(MAX_OUTPUTS_TO_HASH):0] outputs_to_hash;
	reg [SIGNATURE_BITS - 1:0] signature;
	wire [SIGNATURE_BITS - 1:0] next_signature;
	wire done_hashing;
	localparam [1:0] IDLE = 2'b00;
	localparam [1:0] HASH = 2'b01;
	localparam [1:0] DONE = 2'b10;
	assign next_signature = signature ^ cut_req_msg;
	assign done_hashing = ~(outputs_hashed < outputs_to_hash);
	assign next_outputs_hashed = outputs_hashed + 1;
	always @(posedge clk)
		if (reset) begin
			outputs_hashed <= 1'sb0;
			outputs_to_hash <= 1'sb0;
			signature <= 1'sb0;
		end
		else if ((state == IDLE) && lbist_req_val) begin
			signature <= SEED;
			outputs_to_hash <= lbist_req_msg;
		end
		else if (cut_req_val && (state == HASH)) begin
			signature <= {next_signature[SIGNATURE_BITS - 2:0], next_signature[SIGNATURE_BITS - 1]};
			outputs_hashed <= next_outputs_hashed;
		end
		else if (state == DONE)
			outputs_hashed <= 1'sb0;
	always @(posedge clk)
		if (reset)
			state <= IDLE;
		else
			state <= next_state;
	always @(*)
		case (state)
			IDLE:
				if (lbist_req_val)
					next_state = HASH;
				else
					next_state = IDLE;
			HASH:
				if (~done_hashing)
					next_state = HASH;
				else
					next_state = DONE;
			DONE:
				if (lbist_resp_rdy)
					next_state = IDLE;
				else
					next_state = DONE;
			default: next_state = IDLE;
		endcase
	always @(*)
		case (state)
			IDLE: begin
				cut_req_rdy = 0;
				lbist_req_rdy = 1;
				lbist_resp_val = 0;
				lbist_resp_msg = 1'sb0;
			end
			HASH: begin
				cut_req_rdy = 1;
				lbist_req_rdy = 0;
				lbist_resp_val = 0;
				lbist_resp_msg = 1'sb0;
			end
			DONE: begin
				cut_req_rdy = 0;
				lbist_req_rdy = 0;
				lbist_resp_val = 1;
				lbist_resp_msg = signature;
			end
			default: begin
				cut_req_rdy = 0;
				lbist_req_rdy = 1;
				lbist_resp_val = 0;
				lbist_resp_msg = 1'sb0;
			end
		endcase
endmodule
module cmn_reset_synchronizer (
	clk,
	reset,
	s_reset
);
	input wire clk;
	input wire reset;
	output wire s_reset;
	wire out_reset_reg0;
	wire out_reset_reg1;
	cmn_Reg reg0(
		.clk(clk),
		.q(out_reset_reg0),
		.d(reset)
	);
	cmn_Reg reg1(
		.clk(clk),
		.q(out_reset_reg1),
		.d(out_reset_reg0)
	);
	assign s_reset = out_reset_reg1 | reset;
endmodule
module Mem1r1w (
	clk,
	reset,
	write_en,
	write_addr,
	write_data,
	read_en,
	read_addr,
	read_data
);
	parameter p_num_entries = 8;
	parameter p_bit_width = 5;
	parameter p_addr_width = $clog2(p_num_entries);
	input wire clk;
	input wire reset;
	input wire write_en;
	input wire [p_addr_width - 1:0] write_addr;
	input wire [p_bit_width - 1:0] write_data;
	input wire read_en;
	input wire [p_addr_width - 1:0] read_addr;
	output wire [p_bit_width - 1:0] read_data;
	reg [p_bit_width - 1:0] mem [p_num_entries - 1:0];
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	always @(posedge clk)
		if (write_en & ~reset)
			mem[sv2v_cast_32_signed(write_addr)] <= write_data;
	assign read_data = mem[sv2v_cast_32_signed(read_addr)] & {p_bit_width {read_en}};
endmodule
module Synchronizer (
	clk,
	reset,
	d,
	q
);
	parameter p_bit_width = 1;
	input wire clk;
	input wire reset;
	input wire [p_bit_width - 1:0] d;
	output reg [p_bit_width - 1:0] q;
	reg [p_bit_width - 1:0] s;
	always @(posedge clk)
		if (reset) begin
			s <= 0;
			q <= 0;
		end
		else begin
			s <= d;
			q <= s;
		end
endmodule
module BinToGray (
	bin,
	gray
);
	parameter p_bit_width = 3;
	input wire [p_bit_width - 1:0] bin;
	output wire [p_bit_width - 1:0] gray;
	assign gray = bin ^ (bin >> 1);
endmodule
module ResetSync (
	clk,
	async_rst,
	reset
);
	input wire clk;
	input wire async_rst;
	output wire reset;
	reg reg1;
	reg reg2;
	always @(posedge clk or posedge async_rst)
		if (async_rst) begin
			reg1 <= 1'b1;
			reg2 <= 1'b1;
		end
		else begin
			reg1 <= 1'b0;
			reg2 <= reg1;
		end
	assign reset = reg2;
endmodule
module WritePtrBlk (
	clk,
	async_rst,
	b_write_ptr,
	g_write_ptr,
	g_read_ptr_async,
	w_en,
	full
);
	parameter p_num_entries = 8;
	parameter p_ptr_width = $clog2(p_num_entries) + 1;
	parameter p_inc_per_posedge = 1;
	input wire clk;
	input wire async_rst;
	output reg [p_ptr_width - 1:0] b_write_ptr;
	output reg [p_ptr_width - 1:0] g_write_ptr;
	input wire [p_ptr_width - 1:0] g_read_ptr_async;
	input wire w_en;
	output wire full;
	wire reset;
	ResetSync reset_sync(
		.clk(clk),
		.async_rst(async_rst),
		.reset(reset)
	);
	wire [p_ptr_width - 1:0] g_read_ptr;
	Synchronizer #(.p_bit_width(p_ptr_width)) synch(
		.clk(clk),
		.reset(reset),
		.d(g_read_ptr_async),
		.q(g_read_ptr)
	);
	wire [p_ptr_width - 1:0] b_write_ptr_next;
	wire [p_ptr_width - 1:0] g_write_ptr_next;
	assign b_write_ptr_next = b_write_ptr + {{p_ptr_width - 1 {1'b0}}, w_en && !full};
	BinToGray #(.p_bit_width(p_ptr_width)) bin_to_gray(
		.bin(b_write_ptr_next),
		.gray(g_write_ptr_next)
	);
	always @(posedge clk or posedge reset)
		if (reset) begin
			b_write_ptr <= 0;
			g_write_ptr <= 0;
		end
		else begin
			b_write_ptr <= b_write_ptr_next;
			g_write_ptr <= g_write_ptr_next;
		end
	assign full = (g_write_ptr[p_ptr_width - 1:p_ptr_width - 2] == ~g_read_ptr[p_ptr_width - 1:p_ptr_width - 2]) && (g_write_ptr[p_ptr_width - 3:0] == g_read_ptr[p_ptr_width - 3:0]);
endmodule
module ReadPtrBlk (
	clk,
	async_rst,
	b_read_ptr,
	g_read_ptr,
	g_write_ptr_async,
	r_en,
	empty
);
	parameter p_num_entries = 8;
	parameter p_ptr_width = $clog2(p_num_entries) + 1;
	input wire clk;
	input wire async_rst;
	output reg [p_ptr_width - 1:0] b_read_ptr;
	output reg [p_ptr_width - 1:0] g_read_ptr;
	input wire [p_ptr_width - 1:0] g_write_ptr_async;
	input wire r_en;
	output wire empty;
	wire reset;
	ResetSync reset_sync(
		.clk(clk),
		.async_rst(async_rst),
		.reset(reset)
	);
	wire [p_ptr_width - 1:0] g_write_ptr;
	Synchronizer #(.p_bit_width(p_ptr_width)) synch(
		.clk(clk),
		.reset(reset),
		.d(g_write_ptr_async),
		.q(g_write_ptr)
	);
	wire [p_ptr_width - 1:0] b_read_ptr_next;
	wire [p_ptr_width - 1:0] g_read_ptr_next;
	assign b_read_ptr_next = b_read_ptr + {{p_ptr_width - 1 {1'b0}}, r_en && !empty};
	BinToGray #(.p_bit_width(p_ptr_width)) bin_to_gray(
		.bin(b_read_ptr_next),
		.gray(g_read_ptr_next)
	);
	always @(posedge clk or posedge reset)
		if (reset) begin
			b_read_ptr <= 0;
			g_read_ptr <= 0;
		end
		else begin
			b_read_ptr <= b_read_ptr_next;
			g_read_ptr <= g_read_ptr_next;
		end
	assign empty = reset || (g_read_ptr == g_write_ptr);
endmodule
module AsyncFifo (
	i_clk,
	o_clk,
	async_rst,
	istream_msg,
	istream_val,
	istream_rdy,
	ostream_msg,
	ostream_val,
	ostream_rdy
);
	parameter p_num_entries = 8;
	parameter p_bit_width = 8;
	input wire i_clk;
	input wire o_clk;
	input wire async_rst;
	input wire [p_bit_width - 1:0] istream_msg;
	input wire istream_val;
	output wire istream_rdy;
	output wire [p_bit_width - 1:0] ostream_msg;
	output wire ostream_val;
	input wire ostream_rdy;
	localparam ptr_width = $clog2(p_num_entries) + 1;
	wire full;
	wire empty;
	wire [ptr_width - 1:0] g_write_ptr;
	wire [ptr_width - 1:0] g_read_ptr;
	wire [ptr_width - 1:0] b_write_ptr;
	wire [ptr_width - 1:0] b_read_ptr;
	Mem1r1w #(
		.p_num_entries(p_num_entries),
		.p_bit_width(p_bit_width)
	) mem1r1w(
		.clk(i_clk),
		.reset(async_rst),
		.write_en(istream_val && istream_rdy),
		.write_addr(b_write_ptr[ptr_width - 2:0]),
		.write_data(istream_msg),
		.read_en(ostream_val),
		.read_addr(b_read_ptr[ptr_width - 2:0]),
		.read_data(ostream_msg)
	);
	WritePtrBlk #(.p_num_entries(p_num_entries)) write_ptr(
		.g_read_ptr_async(g_read_ptr),
		.clk(i_clk),
		.async_rst(async_rst),
		.w_en(istream_val && istream_rdy),
		.b_write_ptr(b_write_ptr),
		.g_write_ptr(g_write_ptr),
		.full(full)
	);
	ReadPtrBlk #(.p_num_entries(p_num_entries)) read_ptr(
		.g_write_ptr_async(g_write_ptr),
		.clk(o_clk),
		.async_rst(async_rst),
		.r_en(ostream_rdy && ostream_val),
		.b_read_ptr(b_read_ptr),
		.g_read_ptr(g_read_ptr),
		.empty(empty)
	);
	assign istream_rdy = !full;
	assign ostream_val = !empty;
endmodule
module FifoPackager (
	clk,
	reset,
	req_msg,
	req_val,
	req_rdy,
	resp_msg,
	resp_val,
	resp_rdy
);
	parameter p_bit_width = 3;
	parameter p_num_concat = 2;
	input wire clk;
	input wire reset;
	input wire [p_bit_width - 1:0] req_msg;
	input wire req_val;
	output wire req_rdy;
	output reg [(p_bit_width * 2) - 1:0] resp_msg;
	output wire resp_val;
	input wire resp_rdy;
	reg [p_bit_width - 1:0] out [0:p_num_concat - 1];
	reg [$clog2(p_num_concat):0] counter;
	always @(*) begin : sv2v_autoblock_1
		reg signed [31:0] i;
		for (i = 0; i < p_num_concat; i = i + 1)
			resp_msg[i * p_bit_width+:p_bit_width] = out[i];
	end
	assign resp_val = counter >= p_num_concat;
	assign req_rdy = counter < p_num_concat;
	always @(posedge clk)
		if (reset) begin
			begin : sv2v_autoblock_2
				reg signed [31:0] i;
				for (i = 0; i < p_num_concat; i = i + 1)
					out[i] <= 1'sb0;
			end
			counter <= 1'sb0;
		end
		else begin
			if (req_val && (counter < p_num_concat)) begin
				out[counter] <= req_msg;
				counter <= counter + 1;
			end
			if ((counter >= p_num_concat) && resp_rdy)
				counter <= 0;
		end
endmodule
module tapein1_sp25_top (
	clk,
	reset,
	cs,
	mosi,
	miso,
	sclk,
	minion_parity,
	adapter_parity,
	ext_clk,
	async_fifo_recv_msg,
	async_fifo_recv_val,
	async_fifo_recv_rdy
);
	parameter signed [31:0] FIFO_ENTRY_BITS = 8;
	input wire clk;
	input wire reset;
	input wire cs;
	input wire mosi;
	output wire miso;
	input wire sclk;
	output wire minion_parity;
	output wire adapter_parity;
	input wire ext_clk;
	input wire [FIFO_ENTRY_BITS - 1:0] async_fifo_recv_msg;
	input wire async_fifo_recv_val;
	output wire async_fifo_recv_rdy;
	localparam signed [31:0] ADDR_BITS = 4;
	localparam signed [31:0] DATA_BITS = 16;
	localparam signed [31:0] SPI_PACKET_BITS = DATA_BITS + ADDR_BITS;
	localparam signed [31:0] ROUTER_SIZE = 1 << ADDR_BITS;
	localparam signed [31:0] ROUTER_PACKET_BITS = DATA_BITS + ADDR_BITS;
	localparam signed [31:0] ARBITER_SIZE = ROUTER_SIZE;
	localparam signed [31:0] ARBITER_PACKET_BITS = DATA_BITS;
	localparam signed [31:0] INPUT_XBAR_INPUTS = 3;
	localparam signed [31:0] INPUT_XBAR_OUTPUTS = 3;
	localparam signed [31:0] INPUT_XBAR_BITS = DATA_BITS;
	localparam signed [31:0] INPUT_XBAR_CONTROL_BITS = $clog2(32'sd3 * 32'sd3);
	localparam signed [31:0] CLASSIFIER_XBAR_INPUTS = 3;
	localparam signed [31:0] CLASSIFIER_XBAR_OUTPUTS = 3;
	localparam signed [31:0] CLASSIFIER_XBAR_BITS = DATA_BITS;
	localparam signed [31:0] CLASSIFIER_XBAR_CONTROL_BITS = $clog2(32'sd3 * 32'sd3);
	localparam signed [31:0] OUTPUT_XBAR_INPUTS = 2;
	localparam signed [31:0] OUTPUT_XBAR_OUTPUTS = 2;
	localparam signed [31:0] OUTPUT_XBAR_BITS = 1;
	localparam signed [31:0] OUTPUT_XBAR_CONTROL_BITS = $clog2(32'sd2 * 32'sd2);
	localparam signed [31:0] FFT1_SAMPLES = 32;
	localparam signed [31:0] FFT1_DECIMAL_PT = 8;
	localparam signed [31:0] FFT2_SAMPLES = 32;
	localparam signed [31:0] FFT2_DECIMAL_PT = 8;
	localparam signed [31:0] CLASSIFIER_SAMPLES = 16;
	localparam signed [31:0] CLASSIFIER_BITS = 16;
	localparam signed [31:0] CLASSIFIER_DECIMAL_PT = 8;
	localparam signed [31:0] SEED_BITS = DATA_BITS;
	localparam signed [31:0] SIGNATURE_BITS = DATA_BITS;
	localparam signed [31:0] NUM_SEEDS = 2;
	localparam signed [31:0] NUM_HASHES = 80;
	localparam signed [31:0] MAX_OUTPUTS_TO_HASH = 100;
	localparam [(NUM_SEEDS * SEED_BITS) - 1:0] LFSR_SEEDS = 32'b00000000000000000000000000000000;
	localparam [(NUM_SEEDS * SIGNATURE_BITS) - 1:0] EXPECTED_SIGNATURES = 32'b11001110011110111100101001001101;
	localparam signed [31:0] MISR_SEED = 1'sb0;
	localparam signed [31:0] MISR_MSG_BITS = 7;
	localparam signed [31:0] FIFO_DEPTH = 10;
	localparam signed [31:0] PACKAGER_BITS = FIFO_ENTRY_BITS;
	localparam signed [31:0] PACKAGER_CONCAT = 2;
	wire [(ADDR_BITS + DATA_BITS) - 1:0] spi_recv_msg;
	wire spi_recv_rdy;
	wire spi_recv_val;
	wire [(ADDR_BITS + DATA_BITS) - 1:0] spi_send_msg;
	wire spi_send_rdy;
	wire spi_send_val;
	wire [(ROUTER_SIZE * ROUTER_PACKET_BITS) - 1:0] router_msg;
	wire [0:ROUTER_SIZE - 1] router_rdy;
	wire [0:ROUTER_SIZE - 1] router_val;
	wire [15:0] Router_to_InputXbar_msg;
	wire Router_to_InputXbar_val;
	wire Router_to_InputXbar_rdy;
	wire [15:0] Router_to_ClassifierXbar_msg;
	wire Router_to_ClassifierXbar_val;
	wire Router_to_ClassifierXbar_rdy;
	wire [0:0] Router_to_OutputXbar_msg;
	wire Router_to_OutputXbar_rdy;
	wire Router_to_OutputXbar_val;
	wire [15:0] Router_to_Arbiter_msg;
	wire Router_to_Arbiter_val;
	wire Router_to_Arbiter_rdy;
	wire [(ARBITER_SIZE * ARBITER_PACKET_BITS) - 1:0] arbiter_msg;
	wire [0:ARBITER_SIZE - 1] arbiter_rdy;
	wire [0:ARBITER_SIZE - 1] arbiter_val;
	wire [(INPUT_XBAR_INPUTS * INPUT_XBAR_BITS) - 1:0] input_xbar_recv_msg;
	wire [0:2] input_xbar_recv_rdy;
	wire [0:2] input_xbar_recv_val;
	wire [(INPUT_XBAR_OUTPUTS * INPUT_XBAR_BITS) - 1:0] input_xbar_send_msg;
	wire [0:2] input_xbar_send_rdy;
	wire [0:2] input_xbar_send_val;
	wire [INPUT_XBAR_CONTROL_BITS - 1:0] input_xbar_control_msg;
	wire input_xbar_control_rdy;
	wire input_xbar_control_val;
	wire [15:0] InputXbar_to_Arbiter_msg;
	wire InputXbar_to_Arbiter_val;
	wire InputXbar_to_Arbiter_rdy;
	wire [(CLASSIFIER_XBAR_INPUTS * CLASSIFIER_XBAR_BITS) - 1:0] classifier_xbar_recv_msg;
	wire [0:2] classifier_xbar_recv_val;
	wire [0:2] classifier_xbar_recv_rdy;
	wire [(CLASSIFIER_XBAR_OUTPUTS * CLASSIFIER_XBAR_BITS) - 1:0] classifier_xbar_send_msg;
	wire [0:2] classifier_xbar_send_val;
	wire [0:2] classifier_xbar_send_rdy;
	wire [CLASSIFIER_XBAR_CONTROL_BITS - 1:0] classifier_xbar_control_msg;
	wire classifier_xbar_control_rdy;
	wire classifier_xbar_control_val;
	wire [15:0] ClassifierXbar_to_Arbiter_msg;
	wire ClassifierXbar_to_Arbiter_val;
	wire ClassifierXbar_to_Arbiter_rdy;
	wire [0:1] output_xbar_recv_msg;
	wire [0:1] output_xbar_recv_rdy;
	wire [0:1] output_xbar_recv_val;
	wire [0:1] output_xbar_send_msg;
	wire [0:1] output_xbar_send_rdy;
	wire [0:1] output_xbar_send_val;
	wire [OUTPUT_XBAR_CONTROL_BITS - 1:0] output_xbar_control_msg;
	wire output_xbar_control_rdy;
	wire output_xbar_control_val;
	wire [15:0] OutputXbar_to_Arbiter_msg;
	wire OutputXbar_to_Arbiter_val;
	wire OutputXbar_to_Arbiter_rdy;
	wire [15:0] fft1_deserializer_recv_msg;
	wire fft1_deserializer_recv_val;
	wire fft1_deserializer_recv_rdy;
	wire [15:0] fft1_serializer_send_msg;
	wire fft1_serializer_send_val;
	wire fft1_serializer_send_rdy;
	wire [(FFT1_SAMPLES * DATA_BITS) - 1:0] fft1_recv_msg;
	wire fft1_recv_val;
	wire fft1_recv_rdy;
	wire [(FFT1_SAMPLES * DATA_BITS) - 1:0] fft1_send_msg;
	wire fft1_send_val;
	wire fft1_send_rdy;
	wire [15:0] fft2_deserializer_recv_msg;
	wire fft2_deserializer_recv_val;
	wire fft2_deserializer_recv_rdy;
	wire [15:0] fft2_serializer_send_msg;
	wire fft2_serializer_send_val;
	wire fft2_serializer_send_rdy;
	wire [(FFT2_SAMPLES * DATA_BITS) - 1:0] fft2_recv_msg;
	wire fft2_recv_val;
	wire fft2_recv_rdy;
	wire [(FFT2_SAMPLES * DATA_BITS) - 1:0] fft2_send_msg;
	wire fft2_send_val;
	wire fft2_send_rdy;
	wire [15:0] classifier_deserializer_recv_msg;
	wire classifier_deserializer_recv_val;
	wire classifier_deserializer_recv_rdy;
	wire [(CLASSIFIER_SAMPLES * DATA_BITS) - 1:0] classifier_recv_msg;
	wire classifier_recv_val;
	wire classifier_recv_rdy;
	wire [15:0] classifier_config_msg [0:2];
	wire classifier_config_rdy [0:2];
	wire classifier_config_val [0:2];
	wire classifier_send_msg;
	wire classifier_send_val;
	wire classifier_send_rdy;
	wire lbist_req_val;
	wire lbist_req_rdy;
	wire lbist_resp_val;
	wire [1:0] lbist_resp_msg;
	wire lbist_resp_rdy;
	wire ctrl_lfsr_resp_val;
	wire [15:0] ctrl_lfsr_resp_msg;
	wire ctrl_lfsr_resp_rdy;
	wire ctrl_misr_req_val;
	wire [MISR_MSG_BITS:0] ctrl_misr_req_msg;
	wire ctrl_misr_req_rdy;
	wire lfsr_cut_reset;
	wire lfsr_resp_val;
	wire [15:0] lfsr_resp_msg;
	wire lfsr_resp_rdy;
	wire cut_misr_resp_val;
	wire [15:0] cut_misr_resp_msg;
	wire cut_misr_resp_rdy;
	wire misr_resp_val;
	wire [15:0] misr_resp_msg;
	wire misr_resp_rdy;
	wire [FIFO_ENTRY_BITS - 1:0] async_fifo_send_msg;
	wire async_fifo_send_val;
	wire async_fifo_send_rdy;
	wire [15:0] packager_send_msg;
	wire packager_send_val;
	wire packager_send_rdy;
	spi_Minion #(
		.BIT_WIDTH(SPI_PACKET_BITS),
		.N_SAMPLES(1)
	) minion(
		.clk(clk),
		.reset(reset),
		.cs(cs),
		.mosi(mosi),
		.miso(miso),
		.sclk(sclk),
		.recv_msg(spi_recv_msg),
		.recv_rdy(spi_recv_rdy),
		.recv_val(spi_recv_val),
		.send_msg(spi_send_msg),
		.send_rdy(spi_send_rdy),
		.send_val(spi_send_val),
		.minion_parity(minion_parity),
		.adapter_parity(adapter_parity)
	);
	arbiter_router_Router #(
		.nbits(ROUTER_PACKET_BITS),
		.noutputs(ROUTER_SIZE)
	) router(
		.clk(clk),
		.reset(reset),
		.istream_val(spi_send_val),
		.istream_msg(spi_send_msg),
		.istream_rdy(spi_send_rdy),
		.ostream_val(router_val),
		.ostream_msg(router_msg),
		.ostream_rdy(router_rdy)
	);
	arbiter_router_Arbiter #(
		.nbits(ARBITER_PACKET_BITS),
		.ninputs(ARBITER_SIZE)
	) arbiter(
		.clk(clk),
		.reset(reset),
		.istream_val(arbiter_val),
		.istream_msg(arbiter_msg),
		.istream_rdy(arbiter_rdy),
		.ostream_val(spi_recv_val),
		.ostream_msg(spi_recv_msg),
		.ostream_rdy(spi_recv_rdy)
	);
	crossbars_Blocking #(
		.BIT_WIDTH(INPUT_XBAR_BITS),
		.N_INPUTS(INPUT_XBAR_INPUTS),
		.N_OUTPUTS(INPUT_XBAR_OUTPUTS)
	) input_xbar(
		.clk(clk),
		.reset(reset),
		.recv_msg(input_xbar_recv_msg),
		.recv_val(input_xbar_recv_val),
		.recv_rdy(input_xbar_recv_rdy),
		.send_msg(input_xbar_send_msg),
		.send_val(input_xbar_send_val),
		.send_rdy(input_xbar_send_rdy),
		.control(input_xbar_control_msg),
		.control_rdy(input_xbar_control_rdy),
		.control_val(input_xbar_control_val)
	);
	crossbars_Blocking #(
		.BIT_WIDTH(CLASSIFIER_XBAR_BITS),
		.N_INPUTS(CLASSIFIER_XBAR_INPUTS),
		.N_OUTPUTS(CLASSIFIER_XBAR_OUTPUTS)
	) classifier_xbar(
		.clk(clk),
		.reset(reset),
		.recv_msg(classifier_xbar_recv_msg),
		.recv_val(classifier_xbar_recv_val),
		.recv_rdy(classifier_xbar_recv_rdy),
		.send_msg(classifier_xbar_send_msg),
		.send_val(classifier_xbar_send_val),
		.send_rdy(classifier_xbar_send_rdy),
		.control(classifier_xbar_control_msg),
		.control_rdy(classifier_xbar_control_rdy),
		.control_val(classifier_xbar_control_val)
	);
	crossbars_Blocking #(
		.BIT_WIDTH(OUTPUT_XBAR_BITS),
		.N_INPUTS(OUTPUT_XBAR_INPUTS),
		.N_OUTPUTS(OUTPUT_XBAR_OUTPUTS)
	) output_xbar(
		.clk(clk),
		.reset(reset),
		.recv_msg(output_xbar_recv_msg),
		.recv_val(output_xbar_recv_val),
		.recv_rdy(output_xbar_recv_rdy),
		.send_msg(output_xbar_send_msg),
		.send_val(output_xbar_send_val),
		.send_rdy(output_xbar_send_rdy),
		.control(output_xbar_control_msg),
		.control_rdy(output_xbar_control_rdy),
		.control_val(output_xbar_control_val)
	);
	serdes_Deserializer #(
		.N_SAMPLES(FFT1_SAMPLES),
		.BIT_WIDTH(DATA_BITS)
	) fft1_deserializer(
		.clk(clk),
		.reset(reset),
		.recv_val(fft1_deserializer_recv_val),
		.recv_rdy(fft1_deserializer_recv_rdy),
		.recv_msg(fft1_deserializer_recv_msg),
		.send_val(fft1_recv_val),
		.send_rdy(fft1_recv_rdy),
		.send_msg(fft1_recv_msg)
	);
	serdes_Serializer #(
		.N_SAMPLES(16),
		.BIT_WIDTH(DATA_BITS)
	) fft1_serializer(
		.clk(clk),
		.reset(reset),
		.send_val(fft1_serializer_send_val),
		.send_rdy(fft1_serializer_send_rdy),
		.send_msg(fft1_serializer_send_msg),
		.recv_val(fft1_send_val),
		.recv_rdy(fft1_send_rdy),
		.recv_msg(fft1_send_msg[256+:256])
	);
	genvar i;
	generate
		for (i = 16; i < 32; i = i + 1) begin : genblk1
			wire fft1_msg_unused = &{1'b0, fft1_send_msg[(31 - i) * DATA_BITS+:DATA_BITS], 1'b0};
		end
	endgenerate
	fft_pease_FFT #(
		.BIT_WIDTH(DATA_BITS),
		.DECIMAL_PT(FFT1_DECIMAL_PT),
		.N_SAMPLES(FFT1_SAMPLES)
	) fft1(
		.reset(reset),
		.clk(clk),
		.recv_msg(fft1_recv_msg),
		.recv_val(fft1_recv_val),
		.recv_rdy(fft1_recv_rdy),
		.send_msg(fft1_send_msg),
		.send_val(fft1_send_val),
		.send_rdy(fft1_send_rdy)
	);
	serdes_Deserializer #(
		.N_SAMPLES(FFT2_SAMPLES),
		.BIT_WIDTH(DATA_BITS)
	) fft2_deserializer(
		.clk(clk),
		.reset(reset),
		.recv_val(fft2_deserializer_recv_val),
		.recv_rdy(fft2_deserializer_recv_rdy),
		.recv_msg(fft2_deserializer_recv_msg),
		.send_val(fft2_recv_val),
		.send_rdy(fft2_recv_rdy),
		.send_msg(fft2_recv_msg)
	);
	serdes_Serializer #(
		.N_SAMPLES(16),
		.BIT_WIDTH(DATA_BITS)
	) fft2_serializer(
		.clk(clk),
		.reset(reset),
		.send_val(fft2_serializer_send_val),
		.send_rdy(fft2_serializer_send_rdy),
		.send_msg(fft2_serializer_send_msg),
		.recv_val(fft2_send_val),
		.recv_rdy(fft2_send_rdy),
		.recv_msg(fft2_send_msg[256+:256])
	);
	generate
		for (i = 16; i < 32; i = i + 1) begin : genblk2
			wire fft2_msg_unused = &{1'b0, fft2_send_msg[(31 - i) * DATA_BITS+:DATA_BITS], 1'b0};
		end
	endgenerate
	fft_pease_FFT #(
		.BIT_WIDTH(DATA_BITS),
		.DECIMAL_PT(FFT2_DECIMAL_PT),
		.N_SAMPLES(FFT2_SAMPLES)
	) fft2(
		.reset(reset),
		.clk(clk),
		.recv_msg(fft2_recv_msg),
		.recv_val(fft2_recv_val),
		.recv_rdy(fft2_recv_rdy),
		.send_msg(fft2_send_msg),
		.send_val(fft2_send_val),
		.send_rdy(fft2_send_rdy)
	);
	serdes_Deserializer #(
		.N_SAMPLES(CLASSIFIER_SAMPLES),
		.BIT_WIDTH(DATA_BITS)
	) classifier_deserializer(
		.clk(clk),
		.reset(reset),
		.recv_val(classifier_deserializer_recv_val),
		.recv_rdy(classifier_deserializer_recv_rdy),
		.recv_msg(classifier_deserializer_recv_msg),
		.send_val(classifier_recv_val),
		.send_rdy(classifier_recv_rdy),
		.send_msg(classifier_recv_msg)
	);
	classifier_Classifier #(
		.BIT_WIDTH(CLASSIFIER_BITS),
		.DECIMAL_PT(CLASSIFIER_DECIMAL_PT),
		.N_SAMPLES(CLASSIFIER_SAMPLES)
	) classifier(
		.clk(clk),
		.reset(reset),
		.recv_rdy(classifier_recv_rdy),
		.recv_val(classifier_recv_val),
		.recv_msg(classifier_recv_msg),
		.cutoff_freq_rdy(classifier_config_rdy[0]),
		.cutoff_freq_val(classifier_config_val[0]),
		.cutoff_freq_msg(classifier_config_msg[0]),
		.cutoff_mag_rdy(classifier_config_rdy[1]),
		.cutoff_mag_val(classifier_config_val[1]),
		.cutoff_mag_msg(classifier_config_msg[1]),
		.sampling_freq_rdy(classifier_config_rdy[2]),
		.sampling_freq_val(classifier_config_val[2]),
		.sampling_freq_msg(classifier_config_msg[2]),
		.send_rdy(classifier_send_rdy),
		.send_val(classifier_send_val),
		.send_msg(classifier_send_msg)
	);
	lbist_controller #(
		.SEED_BITS(SEED_BITS),
		.SIGNATURE_BITS(SIGNATURE_BITS),
		.NUM_SEEDS(NUM_SEEDS),
		.NUM_HASHES(NUM_HASHES),
		.MAX_OUTPUTS_TO_HASH(MAX_OUTPUTS_TO_HASH),
		.MISR_MSG_BITS(MISR_MSG_BITS),
		.LFSR_SEEDS(LFSR_SEEDS),
		.EXPECTED_SIGNATURES(EXPECTED_SIGNATURES)
	) lbist_controller(
		.clk(clk),
		.reset(reset),
		.lbist_req_val(lbist_req_val),
		.lbist_req_rdy(lbist_req_rdy),
		.lbist_resp_val(lbist_resp_val),
		.lbist_resp_msg(lbist_resp_msg),
		.lbist_resp_rdy(lbist_resp_rdy),
		.lfsr_resp_val(ctrl_lfsr_resp_val),
		.lfsr_resp_msg(ctrl_lfsr_resp_msg),
		.lfsr_resp_rdy(ctrl_lfsr_resp_rdy),
		.lfsr_cut_reset(lfsr_cut_reset),
		.misr_req_val(ctrl_misr_req_val),
		.misr_req_msg(ctrl_misr_req_msg),
		.misr_req_rdy(ctrl_misr_req_rdy),
		.misr_resp_val(misr_resp_val),
		.misr_resp_msg(misr_resp_msg),
		.misr_resp_rdy(misr_resp_rdy)
	);
	lfsr_galois #(.LFSR_MSG_BITS(SEED_BITS)) lfsr(
		.clk(clk),
		.reset(reset || lfsr_cut_reset),
		.req_val(ctrl_lfsr_resp_val),
		.req_msg(ctrl_lfsr_resp_msg),
		.req_rdy(ctrl_lfsr_resp_rdy),
		.resp_rdy(lfsr_resp_rdy),
		.resp_val(lfsr_resp_val),
		.resp_msg(lfsr_resp_msg)
	);
	misr #(
		.CUT_MSG_BITS(SIGNATURE_BITS),
		.SIGNATURE_BITS(SIGNATURE_BITS),
		.MAX_OUTPUTS_TO_HASH(MAX_OUTPUTS_TO_HASH),
		.LBIST_MSG_BITS(MISR_MSG_BITS),
		.SEED(MISR_SEED)
	) misr(
		.clk(clk),
		.reset(reset),
		.cut_req_val(cut_misr_resp_val),
		.cut_req_msg(cut_misr_resp_msg),
		.cut_req_rdy(cut_misr_resp_rdy),
		.lbist_req_val(ctrl_misr_req_val),
		.lbist_req_msg(ctrl_misr_req_msg),
		.lbist_req_rdy(ctrl_misr_req_rdy),
		.lbist_resp_val(misr_resp_val),
		.lbist_resp_msg(misr_resp_msg),
		.lbist_resp_rdy(misr_resp_rdy)
	);
	AsyncFifo #(
		.p_num_entries(FIFO_DEPTH),
		.p_bit_width(FIFO_ENTRY_BITS)
	) async_fifo(
		.i_clk(ext_clk),
		.o_clk(clk),
		.async_rst(reset),
		.istream_msg(async_fifo_recv_msg),
		.istream_val(async_fifo_recv_val),
		.istream_rdy(async_fifo_recv_rdy),
		.ostream_msg(async_fifo_send_msg),
		.ostream_val(async_fifo_send_val),
		.ostream_rdy(async_fifo_send_rdy)
	);
	FifoPackager #(
		.p_bit_width(PACKAGER_BITS),
		.p_num_concat(PACKAGER_CONCAT)
	) packager(
		.clk(clk),
		.reset(reset),
		.req_msg(async_fifo_send_msg),
		.req_val(async_fifo_send_val),
		.req_rdy(async_fifo_send_rdy),
		.resp_msg(packager_send_msg),
		.resp_val(packager_send_val),
		.resp_rdy(packager_send_rdy)
	);
	assign lbist_req_val = router_val[0];
	assign router_rdy[0] = lbist_req_rdy;
	assign Router_to_InputXbar_msg = router_msg[((ROUTER_SIZE - 2) * ROUTER_PACKET_BITS) + (ROUTER_PACKET_BITS - 1)-:ROUTER_PACKET_BITS];
	assign Router_to_InputXbar_val = router_val[1];
	assign router_rdy[1] = Router_to_InputXbar_rdy;
	assign input_xbar_control_msg = router_msg[((ROUTER_SIZE - 3) * ROUTER_PACKET_BITS) + (INPUT_XBAR_CONTROL_BITS - 1)-:INPUT_XBAR_CONTROL_BITS];
	assign input_xbar_control_val = router_val[2];
	assign router_rdy[2] = input_xbar_control_rdy;
	assign Router_to_ClassifierXbar_msg = router_msg[((ROUTER_SIZE - 4) * ROUTER_PACKET_BITS) + (ROUTER_PACKET_BITS - 1)-:ROUTER_PACKET_BITS];
	assign Router_to_ClassifierXbar_val = router_val[3];
	assign router_rdy[3] = Router_to_Arbiter_rdy;
	assign classifier_xbar_control_msg = router_msg[((ROUTER_SIZE - 5) * ROUTER_PACKET_BITS) + (CLASSIFIER_XBAR_CONTROL_BITS - 1)-:CLASSIFIER_XBAR_CONTROL_BITS];
	assign classifier_xbar_control_val = router_val[4];
	assign router_rdy[4] = classifier_xbar_control_rdy;
	assign classifier_config_msg[0] = router_msg[((ROUTER_SIZE - 6) * ROUTER_PACKET_BITS) + 15-:DATA_BITS];
	assign classifier_config_val[0] = router_val[5];
	assign router_rdy[5] = classifier_config_rdy[0];
	assign classifier_config_msg[1] = router_msg[((ROUTER_SIZE - 7) * ROUTER_PACKET_BITS) + 15-:DATA_BITS];
	assign classifier_config_val[1] = router_val[6];
	assign router_rdy[6] = classifier_config_rdy[1];
	assign classifier_config_msg[2] = router_msg[((ROUTER_SIZE - 8) * ROUTER_PACKET_BITS) + 15-:DATA_BITS];
	assign classifier_config_val[2] = router_val[7];
	assign router_rdy[7] = classifier_config_rdy[2];
	assign Router_to_OutputXbar_msg = router_msg[(ROUTER_SIZE - 9) * ROUTER_PACKET_BITS];
	assign Router_to_OutputXbar_val = router_val[8];
	assign router_rdy[8] = Router_to_OutputXbar_rdy;
	assign output_xbar_control_msg = router_msg[((ROUTER_SIZE - 10) * ROUTER_PACKET_BITS) + (OUTPUT_XBAR_CONTROL_BITS - 1)-:OUTPUT_XBAR_CONTROL_BITS];
	assign output_xbar_control_val = router_val[9];
	assign router_rdy[9] = output_xbar_control_rdy;
	assign Router_to_Arbiter_msg = router_msg[((ROUTER_SIZE - 11) * ROUTER_PACKET_BITS) + 15-:ARBITER_PACKET_BITS];
	assign Router_to_Arbiter_val = router_val[10];
	assign router_rdy[10] = Router_to_Arbiter_rdy;
	generate
		for (i = 11; i < ROUTER_SIZE; i = i + 1) begin : genblk3
			assign router_rdy[i] = 1'b0;
		end
	endgenerate
	assign input_xbar_recv_msg[32+:INPUT_XBAR_BITS] = lfsr_resp_msg;
	assign input_xbar_recv_val[0] = lfsr_resp_val;
	assign lfsr_resp_rdy = input_xbar_recv_rdy[0];
	assign input_xbar_recv_msg[16+:INPUT_XBAR_BITS] = packager_send_msg;
	assign input_xbar_recv_val[1] = packager_send_val;
	assign packager_send_rdy = input_xbar_recv_rdy[1];
	assign input_xbar_recv_msg[0+:INPUT_XBAR_BITS] = Router_to_InputXbar_msg;
	assign input_xbar_recv_val[2] = Router_to_InputXbar_val;
	assign Router_to_InputXbar_rdy = input_xbar_recv_rdy[2];
	assign fft1_deserializer_recv_msg = input_xbar_send_msg[32+:INPUT_XBAR_BITS];
	assign fft1_deserializer_recv_val = input_xbar_send_val[0];
	assign input_xbar_send_rdy[0] = fft1_deserializer_recv_rdy;
	assign fft2_deserializer_recv_msg = input_xbar_send_msg[16+:INPUT_XBAR_BITS];
	assign fft2_deserializer_recv_val = input_xbar_send_val[1];
	assign input_xbar_send_rdy[1] = fft2_deserializer_recv_rdy;
	assign InputXbar_to_Arbiter_msg = input_xbar_send_msg[0+:INPUT_XBAR_BITS];
	assign InputXbar_to_Arbiter_val = input_xbar_send_val[2];
	assign input_xbar_send_rdy[2] = InputXbar_to_Arbiter_rdy;
	assign classifier_xbar_recv_msg[32+:CLASSIFIER_XBAR_BITS] = fft1_serializer_send_msg;
	assign classifier_xbar_recv_val[0] = fft1_serializer_send_val;
	assign fft1_serializer_send_rdy = classifier_xbar_recv_rdy[0];
	assign classifier_xbar_recv_msg[16+:CLASSIFIER_XBAR_BITS] = fft2_serializer_send_msg;
	assign classifier_xbar_recv_val[1] = fft2_serializer_send_val;
	assign fft2_serializer_send_rdy = classifier_xbar_recv_rdy[1];
	assign classifier_xbar_recv_msg[0+:CLASSIFIER_XBAR_BITS] = Router_to_ClassifierXbar_msg;
	assign classifier_xbar_recv_val[2] = Router_to_ClassifierXbar_val;
	assign Router_to_ClassifierXbar_rdy = classifier_xbar_recv_rdy[2];
	assign cut_misr_resp_msg = classifier_xbar_send_msg[32+:CLASSIFIER_XBAR_BITS];
	assign cut_misr_resp_val = classifier_xbar_send_val[0];
	assign classifier_xbar_send_rdy[0] = cut_misr_resp_rdy;
	assign classifier_deserializer_recv_msg = classifier_xbar_send_msg[16+:CLASSIFIER_XBAR_BITS];
	assign classifier_deserializer_recv_val = classifier_xbar_send_val[1];
	assign classifier_xbar_send_rdy[1] = classifier_deserializer_recv_rdy;
	assign ClassifierXbar_to_Arbiter_msg = classifier_xbar_send_msg[0+:CLASSIFIER_XBAR_BITS];
	assign ClassifierXbar_to_Arbiter_val = classifier_xbar_send_val[2];
	assign classifier_xbar_send_rdy[2] = ClassifierXbar_to_Arbiter_rdy;
	assign output_xbar_recv_msg[0] = classifier_send_msg;
	assign output_xbar_recv_val[0] = classifier_send_val;
	assign classifier_send_rdy = output_xbar_recv_rdy[0];
	assign output_xbar_recv_msg[1] = Router_to_OutputXbar_msg;
	assign output_xbar_recv_val[1] = Router_to_OutputXbar_val;
	assign Router_to_OutputXbar_rdy = output_xbar_recv_rdy[1];
	assign OutputXbar_to_Arbiter_msg = {15'b000000000000000, output_xbar_send_msg[0]};
	assign OutputXbar_to_Arbiter_val = output_xbar_send_val[0];
	assign output_xbar_send_rdy[0] = OutputXbar_to_Arbiter_rdy;
	assign output_xbar_send_rdy[1] = 1'sb0;
	assign arbiter_msg[(ARBITER_SIZE - 1) * ARBITER_PACKET_BITS+:ARBITER_PACKET_BITS] = Router_to_Arbiter_msg;
	assign arbiter_val[0] = Router_to_Arbiter_val;
	assign Router_to_Arbiter_rdy = arbiter_rdy[0];
	assign arbiter_msg[(ARBITER_SIZE - 2) * ARBITER_PACKET_BITS+:ARBITER_PACKET_BITS] = InputXbar_to_Arbiter_msg;
	assign arbiter_val[1] = InputXbar_to_Arbiter_val;
	assign InputXbar_to_Arbiter_rdy = arbiter_rdy[1];
	assign arbiter_msg[(ARBITER_SIZE - 3) * ARBITER_PACKET_BITS+:ARBITER_PACKET_BITS] = ClassifierXbar_to_Arbiter_msg;
	assign arbiter_val[2] = ClassifierXbar_to_Arbiter_val;
	assign ClassifierXbar_to_Arbiter_rdy = arbiter_rdy[2];
	assign arbiter_msg[(ARBITER_SIZE - 4) * ARBITER_PACKET_BITS+:ARBITER_PACKET_BITS] = OutputXbar_to_Arbiter_msg;
	assign arbiter_val[3] = OutputXbar_to_Arbiter_val;
	assign OutputXbar_to_Arbiter_rdy = arbiter_rdy[3];
	assign arbiter_msg[(ARBITER_SIZE - 5) * ARBITER_PACKET_BITS+:ARBITER_PACKET_BITS] = lbist_resp_msg;
	assign arbiter_val[4] = lbist_resp_val;
	assign lbist_resp_rdy = arbiter_rdy[4];
	generate
		for (i = 5; i < ARBITER_SIZE; i = i + 1) begin : genblk4
			assign arbiter_msg[((ARBITER_SIZE - 1) - i) * ARBITER_PACKET_BITS+:ARBITER_PACKET_BITS] = 16'b0000000000000000;
			assign arbiter_val[i] = 1'b0;
		end
		if (INPUT_XBAR_CONTROL_BITS > DATA_BITS) begin : genblk5
			$error("INPUT_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
		end
		if (CLASSIFIER_XBAR_CONTROL_BITS > DATA_BITS) begin : genblk6
			$error("CLASSIFIER_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
		end
		if (OUTPUT_XBAR_CONTROL_BITS > DATA_BITS) begin : genblk7
			$error("OUTPUT_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
		end
	endgenerate
endmodule
module top_synth (
	clk,
	reset,
	// Clock and Reset Ports
    `ifdef USE_POWER_PINS
        inout vccd1, // User area 1 1.8V supply
        inout vssd1, // User area 1 digital ground
    `endif
	cs,
	mosi,
	miso,
	sclk,
	minion_parity,
	adapter_parity,
	ext_clk,
	async_fifo_recv_msg,
	async_fifo_recv_val,
	async_fifo_recv_rdy
);
	parameter signed [31:0] FIFO_ENTRY_BITS = 8;
	input wire clk;
	input wire reset;
	input wire cs;
	input wire mosi;
	output wire miso;
	input wire sclk;
	output wire minion_parity;
	output wire adapter_parity;
	input wire ext_clk;
	input wire [FIFO_ENTRY_BITS - 1:0] async_fifo_recv_msg;
	input wire async_fifo_recv_val;
	output wire async_fifo_recv_rdy;
	tapein1_sp25_top #(.FIFO_ENTRY_BITS(FIFO_ENTRY_BITS)) top(
		.clk(clk),
		.reset(reset),
		.cs(cs),
		.mosi(mosi),
		.miso(miso),
		.sclk(sclk),
		.minion_parity(minion_parity),
		.adapter_parity(adapter_parity),
		.ext_clk(ext_clk),
		.async_fifo_recv_msg(async_fifo_recv_msg),
		.async_fifo_recv_val(async_fifo_recv_val),
		.async_fifo_recv_rdy(async_fifo_recv_rdy)
	);
endmodule
