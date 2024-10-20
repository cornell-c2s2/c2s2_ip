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
