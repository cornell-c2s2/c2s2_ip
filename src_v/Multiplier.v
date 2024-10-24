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
