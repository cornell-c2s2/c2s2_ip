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
