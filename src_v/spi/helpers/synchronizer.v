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
