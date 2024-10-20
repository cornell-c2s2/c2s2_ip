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
