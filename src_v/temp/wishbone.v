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
