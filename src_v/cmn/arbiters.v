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
module cmn_FixedArbChain (
	kin,
	reqs,
	grants,
	kout
);
	parameter p_num_reqs = 2;
	input wire kin;
	input wire [p_num_reqs - 1:0] reqs;
	output wire [p_num_reqs - 1:0] grants;
	output wire kout;
	wire [p_num_reqs:0] kills;
	assign kills[0] = 1'b0;
	wire [p_num_reqs - 1:0] grants_int;
	genvar i;
	generate
		for (i = 0; i < p_num_reqs; i = i + 1) begin : per_req_logic
			assign grants_int[i] = !kills[i] && reqs[i];
			assign kills[i + 1] = kills[i] || grants_int[i];
		end
	endgenerate
	assign grants = grants_int & {p_num_reqs {~kin}};
	assign kout = kills[p_num_reqs] || kin;
endmodule
module cmn_FixedArb (
	reqs,
	grants
);
	parameter p_num_reqs = 2;
	input wire [p_num_reqs - 1:0] reqs;
	output wire [p_num_reqs - 1:0] grants;
	wire dummy_kout;
	cmn_FixedArbChain #(.p_num_reqs(p_num_reqs)) fixed_arb_chain(
		.kin(1'b0),
		.reqs(reqs),
		.grants(grants),
		.kout(dummy_kout)
	);
endmodule
module cmn_VariableArbChain (
	kin,
	priority_,
	reqs,
	grants,
	kout
);
	parameter p_num_reqs = 2;
	input wire kin;
	input wire [p_num_reqs - 1:0] priority_;
	input wire [p_num_reqs - 1:0] reqs;
	output wire [p_num_reqs - 1:0] grants;
	output wire kout;
	wire [2 * p_num_reqs:0] kills;
	assign kills[0] = 1'b1;
	wire [(2 * p_num_reqs) - 1:0] priority_int;
	assign priority_int = {{p_num_reqs {1'b0}}, priority_};
	wire [(2 * p_num_reqs) - 1:0] reqs_int;
	assign reqs_int = {reqs, reqs};
	wire [(2 * p_num_reqs) - 1:0] grants_int;
	localparam p_num_reqs_x2 = p_num_reqs << 1;
	genvar i;
	generate
		for (i = 0; i < (2 * p_num_reqs); i = i + 1) begin : per_req_logic
			assign grants_int[i] = (priority_int[i] ? reqs_int[i] : !kills[i] && reqs_int[i]);
			assign kills[i + 1] = (priority_int[i] ? grants_int[i] : kills[i] || grants_int[i]);
		end
	endgenerate
	assign grants = (grants_int[p_num_reqs - 1:0] | grants_int[(2 * p_num_reqs) - 1:p_num_reqs]) & {p_num_reqs {~kin}};
	assign kout = kills[2 * p_num_reqs] || kin;
endmodule
module cmn_VariableArb (
	priority_,
	reqs,
	grants
);
	parameter p_num_reqs = 2;
	input wire [p_num_reqs - 1:0] priority_;
	input wire [p_num_reqs - 1:0] reqs;
	output wire [p_num_reqs - 1:0] grants;
	wire dummy_kout;
	cmn_VariableArbChain #(.p_num_reqs(p_num_reqs)) variable_arb_chain(
		.kin(1'b0),
		.priority_(priority_),
		.reqs(reqs),
		.grants(grants),
		.kout(dummy_kout)
	);
endmodule
module cmn_RoundRobinArbChain (
	clk,
	reset,
	kin,
	reqs,
	grants,
	kout
);
	parameter p_num_reqs = 2;
	parameter p_priority_reset_value = 1;
	input wire clk;
	input wire reset;
	input wire kin;
	input wire [p_num_reqs - 1:0] reqs;
	output wire [p_num_reqs - 1:0] grants;
	output wire kout;
	wire priority_en;
	assign priority_en = |grants;
	wire [p_num_reqs - 1:0] priority_next;
	assign priority_next = {grants[p_num_reqs - 2:0], grants[p_num_reqs - 1]};
	wire [p_num_reqs - 1:0] priority_;
	cmn_EnResetReg #(
		.p_nbits(p_num_reqs),
		.p_reset_value(p_priority_reset_value)
	) priority_reg(
		.clk(clk),
		.reset(reset),
		.en(priority_en),
		.d(priority_next),
		.q(priority_)
	);
	cmn_VariableArbChain #(.p_num_reqs(p_num_reqs)) variable_arb_chain(
		.kin(kin),
		.priority_(priority_),
		.reqs(reqs),
		.grants(grants),
		.kout(kout)
	);
endmodule
module cmn_RoundRobinArbEn (
	clk,
	reset,
	en,
	reqs,
	grants
);
	parameter p_num_reqs = 2;
	input wire clk;
	input wire reset;
	input wire en;
	input wire [p_num_reqs - 1:0] reqs;
	output wire [p_num_reqs - 1:0] grants;
	wire priority_en;
	assign priority_en = |grants && en;
	wire [p_num_reqs - 1:0] priority_next;
	assign priority_next = {grants[p_num_reqs - 2:0], grants[p_num_reqs - 1]};
	wire [p_num_reqs - 1:0] priority_;
	cmn_EnResetReg #(
		.p_nbits(p_num_reqs),
		.p_reset_value(1)
	) priority_reg(
		.clk(clk),
		.reset(reset),
		.en(priority_en),
		.d(priority_next),
		.q(priority_)
	);
	wire dummy_kout;
	cmn_VariableArbChain #(.p_num_reqs(p_num_reqs)) variable_arb_chain(
		.kin(1'b0),
		.priority_(priority_),
		.reqs(reqs),
		.grants(grants),
		.kout(dummy_kout)
	);
endmodule
module cmn_RoundRobinArb (
	clk,
	reset,
	reqs,
	grants
);
	parameter p_num_reqs = 2;
	input wire clk;
	input wire reset;
	input wire [p_num_reqs - 1:0] reqs;
	output wire [p_num_reqs - 1:0] grants;
	wire priority_en;
	assign priority_en = |grants;
	wire [p_num_reqs - 1:0] priority_next;
	assign priority_next = {grants[p_num_reqs - 2:0], grants[p_num_reqs - 1]};
	wire [p_num_reqs - 1:0] priority_;
	cmn_EnResetReg #(
		.p_nbits(p_num_reqs),
		.p_reset_value(1)
	) priority_reg(
		.clk(clk),
		.reset(reset),
		.en(priority_en),
		.d(priority_next),
		.q(priority_)
	);
	wire dummy_kout;
	cmn_VariableArbChain #(.p_num_reqs(p_num_reqs)) variable_arb_chain(
		.kin(1'b0),
		.priority_(priority_),
		.reqs(reqs),
		.grants(grants),
		.kout(dummy_kout)
	);
endmodule
