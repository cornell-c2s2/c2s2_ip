module interconnect_fpga_top (
	clk,
	reset,
	cs,
	mosi,
	miso,
	sclk,
	minion_parity,
	adapter_parity
);
	input wire clk;
	input wire reset;
	input wire cs;
	input wire mosi;
	output wire miso;
	input wire sclk;
	output wire minion_parity;
	output wire adapter_parity;
	wire wbs_stb_i;
	wire wbs_cyc_i;
	wire wbs_we_i;
	wire [3:0] wbs_sel_i;
	wire [31:0] wbs_dat_i;
	wire [31:0] wbs_adr_i;
	wire wbs_ack_o;
	wire [31:0] wbs_dat_o;
	wire [22:0] io_oeb;
	wire [4:0] io_out;
	tapeins_sp24_tapein2_Interconnect interconnection(
		.clk(clk),
		.reset(reset),
		.cs(cs),
		.mosi(mosi),
		.miso(miso),
		.sclk(sclk),
		.minion_parity(minion_parity),
		.adapter_parity(adapter_parity),
		.wbs_stb_i(wbs_stb_i),
		.wbs_cyc_i(wbs_cyc_i),
		.wbs_we_i(wbs_we_i),
		.wbs_sel_i(wbs_sel_i),
		.wbs_dat_i(wbs_dat_i),
		.wbs_adr_i(wbs_adr_i),
		.wbs_ack_o(wbs_ack_o),
		.wbs_dat_o(wbs_dat_o),
		.io_oeb(io_oeb),
		.io_out(io_out)
	);
	assign wbs_stb_i = 1'b0;
	assign wbs_cyc_i = 1'b0;
	assign wbs_we_i = 1'b0;
	assign wbs_sel_i = 4'b0000;
	assign wbs_dat_i = 32'b00000000000000000000000000000000;
	assign wbs_adr_i = 32'b00000000000000000000000000000000;
	wire unused_wbs_ack_o;
	wire unused_wbs_dat_o;
	wire unused_io_oeb;
	wire unused_io_out;
	assign unused_wbs_ack_o = wbs_ack_o;
	assign unused_wbs_dat_o = &wbs_dat_o;
	assign unused_io_oeb = &io_oeb;
	assign unused_io_out = &io_out;
endmodule
