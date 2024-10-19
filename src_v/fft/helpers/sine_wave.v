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
