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
