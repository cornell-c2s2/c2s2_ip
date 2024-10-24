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
			reg unused = &sine_wave_in;
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
module cmn_Adder (
	in0,
	in1,
	cin,
	out,
	cout
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	input wire cin;
	output wire [p_nbits - 1:0] out;
	output wire cout;
	assign {cout, out} = (in0 + in1) + {{p_nbits - 1 {1'b0}}, cin};
endmodule
module cmn_SimpleAdder (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire [p_nbits - 1:0] out;
	assign out = in0 + in1;
endmodule
module cmn_Subtractor (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire [p_nbits - 1:0] out;
	assign out = in0 - in1;
endmodule
module cmn_Incrementer (
	in,
	out
);
	parameter p_nbits = 1;
	parameter p_inc_value = 1;
	input wire [p_nbits - 1:0] in;
	output wire [p_nbits - 1:0] out;
	assign out = in + p_inc_value;
endmodule
module cmn_ZeroExtender (
	in,
	out
);
	parameter p_in_nbits = 1;
	parameter p_out_nbits = 8;
	input wire [p_in_nbits - 1:0] in;
	output wire [p_out_nbits - 1:0] out;
	assign out = {{p_out_nbits - p_in_nbits {1'b0}}, in};
endmodule
module cmn_SignExtender (
	in,
	out
);
	parameter p_in_nbits = 1;
	parameter p_out_nbits = 8;
	input wire [p_in_nbits - 1:0] in;
	output wire [p_out_nbits - 1:0] out;
	assign out = {{p_out_nbits - p_in_nbits {in[p_in_nbits - 1]}}, in};
endmodule
module cmn_ZeroComparator (
	in,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in;
	output wire out;
	assign out = in == {p_nbits {1'b0}};
endmodule
module cmn_EqComparator (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire out;
	assign out = in0 == in1;
endmodule
module cmn_LtComparator (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire out;
	assign out = in0 < in1;
endmodule
module cmn_GtComparator (
	in0,
	in1,
	out
);
	parameter p_nbits = 1;
	input wire [p_nbits - 1:0] in0;
	input wire [p_nbits - 1:0] in1;
	output wire out;
	assign out = in0 > in1;
endmodule
module cmn_LeftLogicalShifter (
	in,
	shamt,
	out
);
	parameter p_nbits = 1;
	parameter p_shamt_nbits = 1;
	input wire [p_nbits - 1:0] in;
	input wire [p_shamt_nbits - 1:0] shamt;
	output wire [p_nbits - 1:0] out;
	assign out = in << shamt;
endmodule
module cmn_RightLogicalShifter (
	in,
	shamt,
	out
);
	parameter p_nbits = 1;
	parameter p_shamt_nbits = 1;
	input wire [p_nbits - 1:0] in;
	input wire [p_shamt_nbits - 1:0] shamt;
	output wire [p_nbits - 1:0] out;
	assign out = in >> shamt;
endmodule
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
module tapeins_sp24_tapein2_Interconnect (
	clk,
	reset,
	cs,
	mosi,
	miso,
	sclk,
	minion_parity,
	adapter_parity,
	wbs_stb_i,
	wbs_cyc_i,
	wbs_we_i,
	wbs_sel_i,
	wbs_dat_i,
	wbs_adr_i,
	wbs_ack_o,
	wbs_dat_o,
	io_oeb,
	io_out
);
	input wire clk;
	input wire reset;
	input wire cs;
	input wire mosi;
	output wire miso;
	input wire sclk;
	output wire minion_parity;
	output wire adapter_parity;
	input wire wbs_stb_i;
	input wire wbs_cyc_i;
	input wire wbs_we_i;
	input wire [3:0] wbs_sel_i;
	input wire [31:0] wbs_dat_i;
	input wire [31:0] wbs_adr_i;
	output wire wbs_ack_o;
	output wire [31:0] wbs_dat_o;
	output wire [22:0] io_oeb;
	output wire [4:0] io_out;
	assign io_oeb = 0;
	assign io_out = 0;
	localparam signed [31:0] ADDR_BITS = 4;
	localparam signed [31:0] ROUTER_ARBITER_SIZE = 1 << ADDR_BITS;
	localparam signed [31:0] DATA_BITS = 16;
	wire [(ADDR_BITS + DATA_BITS) - 1:0] spi_recv_msg;
	wire spi_recv_rdy;
	wire spi_recv_val;
	wire [(ADDR_BITS + DATA_BITS) - 1:0] spi_send_msg;
	wire spi_send_rdy;
	wire spi_send_val;
	spi_Minion #(
		.BIT_WIDTH(ADDR_BITS + DATA_BITS),
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
	wire [(ROUTER_ARBITER_SIZE * (ADDR_BITS + DATA_BITS)) - 1:0] router_msg;
	wire [0:ROUTER_ARBITER_SIZE - 1] router_rdy;
	wire [0:ROUTER_ARBITER_SIZE - 1] router_val;
	arbiter_router_Router #(
		.nbits(ADDR_BITS + DATA_BITS),
		.noutputs(ROUTER_ARBITER_SIZE)
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
	wire [(ROUTER_ARBITER_SIZE * DATA_BITS) - 1:0] arbiter_msg;
	wire [0:ROUTER_ARBITER_SIZE - 1] arbiter_rdy;
	wire [0:ROUTER_ARBITER_SIZE - 1] arbiter_val;
	arbiter_router_Arbiter #(
		.nbits(16),
		.ninputs(ROUTER_ARBITER_SIZE)
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
	localparam signed [31:0] XBAR_CTRL_BITS = 4;
	generate
		if (XBAR_CTRL_BITS > DATA_BITS) begin : genblk1
			$error("XBAR_CTRL_BITS must be less than or equal to DATA_BITS");
		end
	endgenerate
	wire [31:0] input_xbar_recv_msg;
	wire [0:1] input_xbar_recv_rdy;
	wire [0:1] input_xbar_recv_val;
	wire [47:0] input_xbar_send_msg;
	wire [0:2] input_xbar_send_rdy;
	wire [0:2] input_xbar_send_val;
	wire [3:0] input_xbar_control_msg;
	wire input_xbar_control_rdy;
	wire input_xbar_control_val;
	wire input_xbar_control_unused = &{1'b0, input_xbar_control_msg[3], 1'b0};
	crossbars_Blocking #(
		.BIT_WIDTH(DATA_BITS),
		.N_INPUTS(2),
		.N_OUTPUTS(3)
	) input_xbar(
		.clk(clk),
		.reset(reset),
		.recv_msg(input_xbar_recv_msg),
		.recv_val(input_xbar_recv_val),
		.recv_rdy(input_xbar_recv_rdy),
		.send_msg(input_xbar_send_msg),
		.send_val(input_xbar_send_val),
		.send_rdy(input_xbar_send_rdy),
		.control(input_xbar_control_msg[2:0]),
		.control_rdy(input_xbar_control_rdy),
		.control_val(input_xbar_control_val)
	);
	wire [47:0] classifier_xbar_recv_msg;
	wire [0:2] classifier_xbar_recv_val;
	wire [0:2] classifier_xbar_recv_rdy;
	wire [47:0] classifier_xbar_send_msg;
	wire [0:2] classifier_xbar_send_val;
	wire [0:2] classifier_xbar_send_rdy;
	wire [3:0] classifier_xbar_control_msg;
	wire classifier_xbar_control_rdy;
	wire classifier_xbar_control_val;
	crossbars_Blocking #(
		.BIT_WIDTH(DATA_BITS),
		.N_INPUTS(3),
		.N_OUTPUTS(3)
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
	wire [0:2] output_xbar_recv_msg;
	wire [0:2] output_xbar_recv_rdy;
	wire [0:2] output_xbar_recv_val;
	wire [0:1] output_xbar_send_msg;
	wire [0:1] output_xbar_send_rdy;
	wire [0:1] output_xbar_send_val;
	wire [3:0] output_xbar_control_msg;
	wire output_xbar_control_rdy;
	wire output_xbar_control_val;
	wire output_xbar_control_unused = &{1'b0, output_xbar_control_msg[1], 1'b0};
	crossbars_Blocking #(
		.BIT_WIDTH(1),
		.N_INPUTS(3),
		.N_OUTPUTS(2)
	) output_xbar(
		.clk(clk),
		.reset(reset),
		.recv_msg(output_xbar_recv_msg),
		.recv_val(output_xbar_recv_val),
		.recv_rdy(output_xbar_recv_rdy),
		.send_msg(output_xbar_send_msg),
		.send_val(output_xbar_send_val),
		.send_rdy(output_xbar_send_rdy),
		.control({output_xbar_control_msg[3:2], output_xbar_control_msg[0]}),
		.control_rdy(output_xbar_control_rdy),
		.control_val(output_xbar_control_val)
	);
	wire [511:0] fft_recv_msg;
	wire fft_recv_val;
	wire fft_recv_rdy;
	serdes_Deserializer #(
		.N_SAMPLES(32),
		.BIT_WIDTH(DATA_BITS)
	) fft_deserializer(
		.clk(clk),
		.reset(reset),
		.recv_val(input_xbar_send_val[2]),
		.recv_rdy(input_xbar_send_rdy[2]),
		.recv_msg(input_xbar_send_msg[0+:DATA_BITS]),
		.send_val(fft_recv_val),
		.send_rdy(fft_recv_rdy),
		.send_msg(fft_recv_msg)
	);
	wire [511:0] fft_send_msg;
	wire fft_send_val;
	wire fft_send_rdy;
	genvar i;
	generate
		for (i = 16; i < 32; i = i + 1) begin : genblk2
			wire fft_msg_unused = &{1'b0, fft_send_msg[(31 - i) * DATA_BITS+:DATA_BITS], 1'b0};
		end
	endgenerate
	serdes_Serializer #(
		.N_SAMPLES(16),
		.BIT_WIDTH(DATA_BITS)
	) fft_serializer(
		.clk(clk),
		.reset(reset),
		.send_val(classifier_xbar_recv_val[2]),
		.send_rdy(classifier_xbar_recv_rdy[2]),
		.send_msg(classifier_xbar_recv_msg[0+:DATA_BITS]),
		.recv_val(fft_send_val),
		.recv_rdy(fft_send_rdy),
		.recv_msg(fft_send_msg[256+:256])
	);
	wire [255:0] classifier_recv_msg;
	wire classifier_recv_val;
	wire classifier_recv_rdy;
	serdes_Deserializer #(
		.N_SAMPLES(16),
		.BIT_WIDTH(DATA_BITS)
	) classifier_deserializer(
		.clk(clk),
		.reset(reset),
		.recv_val(classifier_xbar_send_val[2]),
		.recv_rdy(classifier_xbar_send_rdy[2]),
		.recv_msg(classifier_xbar_send_msg[0+:DATA_BITS]),
		.send_val(classifier_recv_val),
		.send_rdy(classifier_recv_rdy),
		.send_msg(classifier_recv_msg)
	);
	fft_pease_FFT #(
		.BIT_WIDTH(DATA_BITS),
		.DECIMAL_PT(8),
		.N_SAMPLES(32)
	) fft(
		.reset(reset),
		.clk(clk),
		.recv_msg(fft_recv_msg),
		.recv_val(fft_recv_val),
		.recv_rdy(fft_recv_rdy),
		.send_msg(fft_send_msg),
		.send_val(fft_send_val),
		.send_rdy(fft_send_rdy)
	);
	wire [15:0] classifier_config_msg [0:2];
	wire classifier_config_rdy [0:2];
	wire classifier_config_val [0:2];
	classifier_Classifier #(
		.BIT_WIDTH(16),
		.DECIMAL_PT(8),
		.N_SAMPLES(16)
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
		.send_rdy(output_xbar_recv_rdy[2]),
		.send_val(output_xbar_recv_val[2]),
		.send_msg(output_xbar_recv_msg[2])
	);
	wire [95:0] wishbone_ostream_data;
	wire [0:2] wishbone_ostream_val;
	wire [0:2] wishbone_ostream_rdy;
	wire [95:0] wishbone_istream_data;
	wire [0:2] wishbone_istream_val;
	wire [0:2] wishbone_istream_rdy;
	wishbone_Wishbone #(
		.p_num_msgs(3),
		.p_num_istream(3),
		.p_num_ostream(3)
	) wishbone(
		.clk(clk),
		.reset(reset),
		.wbs_stb_i(wbs_stb_i),
		.wbs_cyc_i(wbs_cyc_i),
		.wbs_we_i(wbs_we_i),
		.wbs_sel_i(wbs_sel_i),
		.wbs_dat_i(wbs_dat_i),
		.wbs_adr_i(wbs_adr_i),
		.wbs_ack_o(wbs_ack_o),
		.wbs_dat_o(wbs_dat_o),
		.istream_rdy(wishbone_istream_rdy),
		.istream_val(wishbone_istream_val),
		.ostream_rdy(wishbone_ostream_rdy),
		.ostream_val(wishbone_ostream_val),
		.ostream_data(wishbone_ostream_data),
		.istream_data(wishbone_istream_data)
	);
	assign input_xbar_recv_msg[0+:DATA_BITS] = wishbone_istream_data[79-:DATA_BITS];
	assign input_xbar_recv_val[1] = wishbone_istream_val[0];
	assign wishbone_istream_rdy[0] = input_xbar_recv_rdy[1];
	assign classifier_xbar_recv_msg[DATA_BITS+:DATA_BITS] = wishbone_istream_data[47-:DATA_BITS];
	assign classifier_xbar_recv_val[1] = wishbone_istream_val[1];
	assign wishbone_istream_rdy[1] = classifier_xbar_recv_rdy[1];
	assign output_xbar_recv_msg[1] = wishbone_istream_data[0];
	assign output_xbar_recv_val[1] = wishbone_istream_val[2];
	assign wishbone_istream_rdy[2] = output_xbar_recv_rdy[1];
	wire unused_wishbone_istream_bits = &{1'b0, wishbone_istream_data[95-:16], wishbone_istream_data[63-:16], wishbone_istream_data[31-:31], 1'b0};
	assign wishbone_ostream_data[64+:32] = {{16 {input_xbar_send_msg[31]}}, input_xbar_send_msg[DATA_BITS+:DATA_BITS]};
	assign wishbone_ostream_val[0] = input_xbar_send_val[1];
	assign input_xbar_send_rdy[1] = wishbone_ostream_rdy[0];
	assign wishbone_ostream_data[32+:32] = {{16 {classifier_xbar_send_msg[31]}}, classifier_xbar_send_msg[DATA_BITS+:DATA_BITS]};
	assign wishbone_ostream_val[1] = classifier_xbar_send_val[1];
	assign classifier_xbar_send_rdy[1] = wishbone_ostream_rdy[1];
	assign wishbone_ostream_data[0+:32] = {31'b0000000000000000000000000000000, output_xbar_send_msg[1]};
	assign wishbone_ostream_val[2] = output_xbar_send_val[1];
	assign output_xbar_send_rdy[1] = wishbone_ostream_rdy[2];
	assign input_xbar_recv_msg[DATA_BITS+:DATA_BITS] = router_msg[((ROUTER_ARBITER_SIZE - 1) * (ADDR_BITS + DATA_BITS)) + 15-:DATA_BITS];
	assign input_xbar_recv_val[0] = router_val[0];
	assign router_rdy[0] = input_xbar_recv_rdy[0];
	assign input_xbar_control_msg = router_msg[((ROUTER_ARBITER_SIZE - 2) * (ADDR_BITS + DATA_BITS)) + 3-:XBAR_CTRL_BITS];
	assign input_xbar_control_val = router_val[1];
	assign router_rdy[1] = input_xbar_control_rdy;
	assign classifier_xbar_recv_msg[32+:DATA_BITS] = router_msg[((ROUTER_ARBITER_SIZE - 3) * (ADDR_BITS + DATA_BITS)) + 15-:DATA_BITS];
	assign classifier_xbar_recv_val[0] = router_val[2];
	assign router_rdy[2] = classifier_xbar_recv_rdy[0];
	assign classifier_xbar_control_msg = router_msg[((ROUTER_ARBITER_SIZE - 4) * (ADDR_BITS + DATA_BITS)) + 3-:XBAR_CTRL_BITS];
	assign classifier_xbar_control_val = router_val[3];
	assign router_rdy[3] = classifier_xbar_control_rdy;
	assign output_xbar_recv_msg[0] = router_msg[(ROUTER_ARBITER_SIZE - 5) * (ADDR_BITS + DATA_BITS)];
	assign output_xbar_recv_val[0] = router_val[4];
	assign router_rdy[4] = output_xbar_recv_rdy[0];
	assign output_xbar_control_msg = router_msg[((ROUTER_ARBITER_SIZE - 6) * (ADDR_BITS + DATA_BITS)) + 3-:XBAR_CTRL_BITS];
	assign output_xbar_control_val = router_val[5];
	assign router_rdy[5] = output_xbar_control_rdy;
	assign classifier_config_msg[0] = router_msg[((ROUTER_ARBITER_SIZE - 7) * (ADDR_BITS + DATA_BITS)) + 15-:DATA_BITS];
	assign classifier_config_val[0] = router_val[6];
	assign router_rdy[6] = classifier_config_rdy[0];
	assign classifier_config_msg[1] = router_msg[((ROUTER_ARBITER_SIZE - 8) * (ADDR_BITS + DATA_BITS)) + 15-:DATA_BITS];
	assign classifier_config_val[1] = router_val[7];
	assign router_rdy[7] = classifier_config_rdy[1];
	assign classifier_config_msg[2] = router_msg[((ROUTER_ARBITER_SIZE - 9) * (ADDR_BITS + DATA_BITS)) + 15-:DATA_BITS];
	assign classifier_config_val[2] = router_val[8];
	assign router_rdy[8] = classifier_config_rdy[2];
	assign arbiter_msg[(ROUTER_ARBITER_SIZE - 10) * DATA_BITS+:DATA_BITS] = router_msg[((ROUTER_ARBITER_SIZE - 10) * (ADDR_BITS + DATA_BITS)) + 15-:DATA_BITS];
	assign arbiter_val[9] = router_val[9];
	assign router_rdy[9] = arbiter_rdy[9];
	generate
		for (i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin : genblk3
			assign router_rdy[i] = 1'b0;
		end
	endgenerate
	wire unused_xbar_cfg_bits = &{1'b0, router_msg[((ROUTER_ARBITER_SIZE - 2) * (ADDR_BITS + DATA_BITS)) + 15-:12], router_msg[((ROUTER_ARBITER_SIZE - 4) * (ADDR_BITS + DATA_BITS)) + 15-:12], router_msg[((ROUTER_ARBITER_SIZE - 6) * (ADDR_BITS + DATA_BITS)) + 15-:12], 1'b0};
	wire unused_output_xbar_msg = &{1'b0, router_msg[((ROUTER_ARBITER_SIZE - 5) * (ADDR_BITS + DATA_BITS)) + 15-:15], 1'b0};
	generate
		for (i = 0; i <= 9; i = i + 1) begin : genblk4
			wire unused_router_addr = &{1'b0, router_msg[(((ROUTER_ARBITER_SIZE - 1) - i) * (ADDR_BITS + DATA_BITS)) + (((DATA_BITS + ADDR_BITS) - 1) >= DATA_BITS ? (DATA_BITS + ADDR_BITS) - 1 : (((DATA_BITS + ADDR_BITS) - 1) + (((DATA_BITS + ADDR_BITS) - 1) >= DATA_BITS ? (((DATA_BITS + ADDR_BITS) - 1) - DATA_BITS) + 1 : (DATA_BITS - ((DATA_BITS + ADDR_BITS) - 1)) + 1)) - 1)-:(((DATA_BITS + ADDR_BITS) - 1) >= DATA_BITS ? (((DATA_BITS + ADDR_BITS) - 1) - DATA_BITS) + 1 : (DATA_BITS - ((DATA_BITS + ADDR_BITS) - 1)) + 1)], 1'b0};
		end
	endgenerate
	wire unused_router_val = &{1'b0, router_val[10:ROUTER_ARBITER_SIZE - 1], 1'b0};
	wire unused_router_msg = &{1'b0, router_msg[(ADDR_BITS + DATA_BITS) * ((ROUTER_ARBITER_SIZE - 1) - (10 >= (ROUTER_ARBITER_SIZE - 1) ? 10 : (10 + (10 >= (ROUTER_ARBITER_SIZE - 1) ? 12 - ROUTER_ARBITER_SIZE : ROUTER_ARBITER_SIZE - 10)) - 1))+:(ADDR_BITS + DATA_BITS) * (10 >= (ROUTER_ARBITER_SIZE - 1) ? 12 - ROUTER_ARBITER_SIZE : ROUTER_ARBITER_SIZE - 10)], 1'b0};
	assign arbiter_msg[(ROUTER_ARBITER_SIZE - 1) * DATA_BITS+:DATA_BITS] = input_xbar_send_msg[32+:DATA_BITS];
	assign arbiter_val[0] = input_xbar_send_val[0];
	assign input_xbar_send_rdy[0] = arbiter_rdy[0];
	assign arbiter_msg[(ROUTER_ARBITER_SIZE - 2) * DATA_BITS+:DATA_BITS] = 16'b0000000000000000;
	assign arbiter_val[1] = 1'b0;
	assign arbiter_msg[(ROUTER_ARBITER_SIZE - 3) * DATA_BITS+:DATA_BITS] = classifier_xbar_send_msg[32+:DATA_BITS];
	assign arbiter_val[2] = classifier_xbar_send_val[0];
	assign classifier_xbar_send_rdy[0] = arbiter_rdy[2];
	assign arbiter_msg[(ROUTER_ARBITER_SIZE - 4) * DATA_BITS+:DATA_BITS] = 16'b0000000000000000;
	assign arbiter_val[3] = 1'b0;
	assign arbiter_msg[(ROUTER_ARBITER_SIZE - 5) * DATA_BITS+:DATA_BITS] = {15'b000000000000000, output_xbar_send_msg[0]};
	assign arbiter_val[4] = output_xbar_send_val[0];
	assign output_xbar_send_rdy[0] = arbiter_rdy[4];
	generate
		for (i = 5; i <= 8; i = i + 1) begin : genblk5
			assign arbiter_msg[((ROUTER_ARBITER_SIZE - 1) - i) * DATA_BITS+:DATA_BITS] = 16'b0000000000000000;
			assign arbiter_val[i] = 1'b0;
		end
		for (i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin : genblk6
			assign arbiter_msg[((ROUTER_ARBITER_SIZE - 1) - i) * DATA_BITS+:DATA_BITS] = 16'b0000000000000000;
			assign arbiter_val[i] = 1'b0;
		end
	endgenerate
	wire unused_arbiter_rdy = &{1'b0, arbiter_rdy[1], arbiter_rdy[3], arbiter_rdy[5:8], arbiter_rdy[10:ROUTER_ARBITER_SIZE - 1], 1'b0};
endmodule
