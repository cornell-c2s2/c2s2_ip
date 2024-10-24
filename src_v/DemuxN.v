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
