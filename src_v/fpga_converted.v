//======================================================================
// FPGA Emulation Top Module
//======================================================================


module interconnect_fpga_top (
  input  logic clk,
  input  logic reset,
  input  logic cs,
  input  logic mosi,
  output logic miso,
  input  logic sclk,
  output logic minion_parity,
  output logic adapter_parity
);

  // Connections for unused Wishbone inputs and outputs
  logic wbs_stb_i;
  logic wbs_cyc_i;
  logic wbs_we_i;
  logic [3:0] wbs_sel_i;
  logic [31:0] wbs_dat_i;
  logic [31:0] wbs_adr_i;
  logic wbs_ack_o;
  logic [31:0] wbs_dat_o;
  logic [22:0] io_oeb;
  logic [4:0] io_out;

  tapeins_sp24_tapein2_Interconnect interconnection (
    // SPI Connections
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .mosi(mosi),
    .miso(miso),
    .sclk(sclk),
    .minion_parity(minion_parity),
    .adapter_parity(adapter_parity),

    // Wishbone Connections
    .wbs_stb_i(wbs_stb_i),
    .wbs_cyc_i(wbs_cyc_i),
    .wbs_we_i (wbs_we_i),
    .wbs_sel_i(wbs_sel_i),
    .wbs_dat_i(wbs_dat_i),
    .wbs_adr_i(wbs_adr_i),
    .wbs_ack_o(wbs_ack_o),
    .wbs_dat_o(wbs_dat_o),

    .io_oeb(io_oeb),
    .io_out(io_out)
  );

  // Set wishbone inputs to zero.
  assign wbs_stb_i = 1'b0;
  assign wbs_cyc_i = 1'b0;
  assign wbs_we_i  = 1'b0;
  assign wbs_sel_i = 4'b0;
  assign wbs_dat_i = 32'b0;
  assign wbs_adr_i = 32'b0;

  // Attach wishbone outputs to unused wires.
  wire unused_wbs_ack_o;
  wire unused_wbs_dat_o;
  wire unused_io_oeb;
  wire unused_io_out;

  assign unused_wbs_ack_o = wbs_ack_o;
  assign unused_wbs_dat_o = &wbs_dat_o;
  assign unused_io_oeb = &io_oeb;
  assign unused_io_out = &io_out;

endmodule

module tapeins_sp24_tapein2_Interconnect (
  input logic clk,
  input logic reset,
  input logic cs,
  input logic mosi,
  output logic miso,
  input logic sclk,
  output logic minion_parity,
  output logic adapter_parity,
  // Wishbone Slave ports (WB MI A)
  input logic wbs_stb_i,
  input logic wbs_cyc_i,
  input logic wbs_we_i,
  input logic [3:0] wbs_sel_i,
  input logic [31:0] wbs_dat_i,
  input logic [31:0] wbs_adr_i,
  output logic wbs_ack_o,
  output logic [31:0] wbs_dat_o,
  // These outputs are necessary to set the valid
  // io_oeb and io_out values for the gpios.
  output logic [22:0] io_oeb,
  output logic [4:0] io_out
);
  // NOTE: the bottom of this file describes the address mapping.

  // io_oeb can always be zero as we are using inputs with nopull
  assign io_oeb = 0;
  // gpios 0-4 require output values to be set.
  assign io_out = 0;

  localparam int ADDR_BITS = 4;
  localparam int ROUTER_ARBITER_SIZE = 1 << ADDR_BITS;
  localparam int DATA_BITS = 16;

  logic [ADDR_BITS+DATA_BITS-1:0] spi_recv_msg;
  logic                           spi_recv_rdy;
  logic                           spi_recv_val;
  logic [ADDR_BITS+DATA_BITS-1:0] spi_send_msg;
  logic                           spi_send_rdy;
  logic                           spi_send_val;

  // SPI MINION
  spi_Minion #(
    .BIT_WIDTH(ADDR_BITS + DATA_BITS),
    .N_SAMPLES(1)
  ) minion (
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

  //============================================================================
  // Interconnect 
  //============================================================================

  // ROUTER
  logic [ADDR_BITS + DATA_BITS - 1:0] router_msg[ROUTER_ARBITER_SIZE];
  logic                               router_rdy[ROUTER_ARBITER_SIZE];
  logic                               router_val[ROUTER_ARBITER_SIZE];

  arbiter_router_Router #(
    .nbits(ADDR_BITS + DATA_BITS),
    .noutputs(ROUTER_ARBITER_SIZE)
  ) router (
    .clk(clk),
    .reset(reset),
    .istream_val(spi_send_val),
    .istream_msg(spi_send_msg),
    .istream_rdy(spi_send_rdy),
    .ostream_val(router_val),
    .ostream_msg(router_msg),
    .ostream_rdy(router_rdy)
  );

  // ARBITER
  logic [DATA_BITS-1:0] arbiter_msg[ROUTER_ARBITER_SIZE];
  logic                 arbiter_rdy[ROUTER_ARBITER_SIZE];
  logic                 arbiter_val[ROUTER_ARBITER_SIZE];

  arbiter_router_Arbiter #(
    .nbits  (16),
    .ninputs(ROUTER_ARBITER_SIZE)
  ) arbiter (
    .clk(clk),
    .reset(reset),
    .istream_val(arbiter_val),
    .istream_msg(arbiter_msg),
    .istream_rdy(arbiter_rdy),
    .ostream_val(spi_recv_val),
    .ostream_msg(spi_recv_msg),
    .ostream_rdy(spi_recv_rdy)
  );

  localparam int XBAR_CTRL_BITS = $clog2(3 * 3);

  generate
    if (XBAR_CTRL_BITS > DATA_BITS) begin
    end
  endgenerate

  // INPUT XBAR
  logic [DATA_BITS-1:0] input_xbar_recv_msg[2];
  logic input_xbar_recv_rdy[2];
  logic input_xbar_recv_val[2];

  logic [DATA_BITS-1:0] input_xbar_send_msg[3];
  logic input_xbar_send_rdy[3];
  logic input_xbar_send_val[3];

  logic [XBAR_CTRL_BITS-1:0] input_xbar_control_msg;
  logic input_xbar_control_rdy;
  logic input_xbar_control_val;

  wire input_xbar_control_unused = &{1'b0, input_xbar_control_msg[3], 1'b0};

  crossbars_Blocking #(
    .BIT_WIDTH(DATA_BITS),
    .N_INPUTS (2),
    .N_OUTPUTS(3)
  ) input_xbar (
    .clk(clk),
    .reset(reset),
    .recv_msg(input_xbar_recv_msg),
    .recv_val(input_xbar_recv_val),
    .recv_rdy(input_xbar_recv_rdy),
    .send_msg(input_xbar_send_msg),
    .send_val(input_xbar_send_val),
    .send_rdy(input_xbar_send_rdy),
    // here, we truncate as there are only 2 inputs possible
    // (representable by 1 bit) so the highest bit is ignored.
    .control(input_xbar_control_msg[2:0]),
    .control_rdy(input_xbar_control_rdy),
    .control_val(input_xbar_control_val)
  );

  // CLASSIFIER XBAR
  logic [     DATA_BITS-1:0] classifier_xbar_recv_msg    [3];
  logic                      classifier_xbar_recv_val    [3];
  logic                      classifier_xbar_recv_rdy    [3];

  logic [     DATA_BITS-1:0] classifier_xbar_send_msg    [3];
  logic                      classifier_xbar_send_val    [3];
  logic                      classifier_xbar_send_rdy    [3];

  logic [XBAR_CTRL_BITS-1:0] classifier_xbar_control_msg;
  logic                      classifier_xbar_control_rdy;
  logic                      classifier_xbar_control_val;

  crossbars_Blocking #(
    .BIT_WIDTH(DATA_BITS),
    .N_INPUTS (3),
    .N_OUTPUTS(3)
  ) classifier_xbar (
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

  // OUTPUT XBAR
  logic output_xbar_recv_msg[3];
  logic output_xbar_recv_rdy[3];
  logic output_xbar_recv_val[3];

  logic output_xbar_send_msg[2];
  logic output_xbar_send_rdy[2];
  logic output_xbar_send_val[2];

  logic [XBAR_CTRL_BITS-1:0] output_xbar_control_msg;
  logic output_xbar_control_rdy;
  logic output_xbar_control_val;

  wire output_xbar_control_unused = &{1'b0, output_xbar_control_msg[1], 1'b0};

  // 1 bit output XBAR with classifier output
  crossbars_Blocking #(
    .BIT_WIDTH(1),
    .N_INPUTS (3),
    .N_OUTPUTS(2)
  ) output_xbar (
    .clk(clk),
    .reset(reset),
    .recv_msg(output_xbar_recv_msg),
    .recv_val(output_xbar_recv_val),
    .recv_rdy(output_xbar_recv_rdy),
    .send_msg(output_xbar_send_msg),
    .send_val(output_xbar_send_val),
    .send_rdy(output_xbar_send_rdy),
    .control({
      output_xbar_control_msg[3:2], output_xbar_control_msg[0]
    }),  // here, we discard the second bit (index 1) as there are only 2 outputs
    .control_rdy(output_xbar_control_rdy),
    .control_val(output_xbar_control_val)
  );

  // Deserializer for the FFT, hooked up to output 1 of the input crossbar
  logic [DATA_BITS-1:0] fft_recv_msg [32];
  logic                 fft_recv_val;
  logic                 fft_recv_rdy;

  serdes_Deserializer #(
    .N_SAMPLES(32),
    .BIT_WIDTH(DATA_BITS)
  ) fft_deserializer (
    .clk(clk),
    .reset(reset),
    .recv_val(input_xbar_send_val[2]),
    .recv_rdy(input_xbar_send_rdy[2]),
    .recv_msg(input_xbar_send_msg[2]),
    .send_val(fft_recv_val),
    .send_rdy(fft_recv_rdy),
    .send_msg(fft_recv_msg)
  );

  // Serializer for the FFT, hooked up to input 1 of the classifier crossbar
  logic [DATA_BITS-1:0] fft_send_msg [32];
  logic                 fft_send_val;
  logic                 fft_send_rdy;

  genvar i; 
  generate
    for (i = 16; i < 32; i = i + 1) begin : for_314 
      wire fft_msg_unused = &{1'b0, fft_send_msg[i], 1'b0};
    end
  endgenerate

  serdes_Serializer #(
    // halved here as the upper half of the result of the FFT is just the
    // complex conjugate of the lower half
    .N_SAMPLES(16),
    .BIT_WIDTH(DATA_BITS)
  ) fft_serializer (
    .clk(clk),
    .reset(reset),
    .send_val(classifier_xbar_recv_val[2]),
    .send_rdy(classifier_xbar_recv_rdy[2]),
    .send_msg(classifier_xbar_recv_msg[2]),
    .recv_val(fft_send_val),
    .recv_rdy(fft_send_rdy),
    .recv_msg(fft_send_msg[0:15])
  );

  // Deserializer for the classifier, hooked up to output 1 of the classifier crossbar
  logic [DATA_BITS-1:0] classifier_recv_msg [16];
  logic                 classifier_recv_val;
  logic                 classifier_recv_rdy;

  serdes_Deserializer #(
    .N_SAMPLES(16),
    .BIT_WIDTH(DATA_BITS)
  ) classifier_deserializer (
    .clk(clk),
    .reset(reset),
    .recv_val(classifier_xbar_send_val[2]),
    .recv_rdy(classifier_xbar_send_rdy[2]),
    .recv_msg(classifier_xbar_send_msg[2]),
    .send_val(classifier_recv_val),
    .send_rdy(classifier_recv_rdy),
    .send_msg(classifier_recv_msg)
  );


  // PEASE FFT
  fft_pease_FFT #(
    .BIT_WIDTH (DATA_BITS),
    .DECIMAL_PT(8),
    .N_SAMPLES (32)
  ) fft (
    .reset(reset),
    .clk(clk),
    .recv_msg(fft_recv_msg),
    .recv_val(fft_recv_val),
    .recv_rdy(fft_recv_rdy),
    .send_msg(fft_send_msg),
    .send_val(fft_send_val),
    .send_rdy(fft_send_rdy)
  );

  // CLASSIFIER

  logic [DATA_BITS-1:0] classifier_config_msg[3];
  logic                 classifier_config_rdy[3];
  logic                 classifier_config_val[3];

  classifier_Classifier #(
    .BIT_WIDTH (16),
    .DECIMAL_PT(8),
    .N_SAMPLES (16)
  ) classifier (
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
    // hooked up to input 1 of the output
    .send_rdy(output_xbar_recv_rdy[2]),
    .send_val(output_xbar_recv_val[2]),
    .send_msg(output_xbar_recv_msg[2])
  );

  // WISHBONE HARNESS

  logic [31:0] wishbone_ostream_data[3];
  logic        wishbone_ostream_val [3];
  logic        wishbone_ostream_rdy [3];

  logic [31:0] wishbone_istream_data[3];
  logic        wishbone_istream_val [3];
  logic        wishbone_istream_rdy [3];

  wishbone_Wishbone #(
    .p_num_msgs(3),
    .p_num_istream(3),
    .p_num_ostream(3)
  ) wishbone (
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

  // 3 WB inputs:
  // 0: input xbar inject
  assign input_xbar_recv_msg[1] = wishbone_istream_data[0][DATA_BITS-1:0];
  assign input_xbar_recv_val[1] = wishbone_istream_val[0];
  assign wishbone_istream_rdy[0] = input_xbar_recv_rdy[1];
  // 1: classifier xbar inject
  assign classifier_xbar_recv_msg[1] = wishbone_istream_data[1][DATA_BITS-1:0];
  assign classifier_xbar_recv_val[1] = wishbone_istream_val[1];
  assign wishbone_istream_rdy[1] = classifier_xbar_recv_rdy[1];
  // 2: output xbar inject
  assign output_xbar_recv_msg[1] = wishbone_istream_data[2][0];
  assign output_xbar_recv_val[1] = wishbone_istream_val[2];
  assign wishbone_istream_rdy[2] = output_xbar_recv_rdy[1];

  wire unused_wishbone_istream_bits = &{
    1'b0,
    wishbone_istream_data[0][31:DATA_BITS],
    wishbone_istream_data[1][31:DATA_BITS],
    wishbone_istream_data[2][31:1],
    1'b0
  };

  // 3 WB outputs:
  // 0: input xbar output
  // sign extend the 16 bit data to 32 bits
  assign wishbone_ostream_data[0] = {
    {(32 - DATA_BITS) {input_xbar_send_msg[1][DATA_BITS-1]}}, input_xbar_send_msg[1]
  };
  assign wishbone_ostream_val[0] = input_xbar_send_val[1];
  assign input_xbar_send_rdy[1] = wishbone_ostream_rdy[0];
  // 1: classifier xbar output
  assign wishbone_ostream_data[1] = {
    {(32 - DATA_BITS) {classifier_xbar_send_msg[1][DATA_BITS-1]}}, classifier_xbar_send_msg[1]
  };
  assign wishbone_ostream_val[1] = classifier_xbar_send_val[1];
  assign classifier_xbar_send_rdy[1] = wishbone_ostream_rdy[1];
  // 2: output xbar output
  // zero extend the classifier output to 32 bits
  assign wishbone_ostream_data[2] = {31'b0, output_xbar_send_msg[1]};
  assign wishbone_ostream_val[2] = output_xbar_send_val[1];
  assign output_xbar_send_rdy[1] = wishbone_ostream_rdy[2];

  // 9 inputs:
  // 0: input xbar inject
  assign input_xbar_recv_msg[0] = router_msg[0][DATA_BITS-1:0];
  assign input_xbar_recv_val[0] = router_val[0];
  assign router_rdy[0] = input_xbar_recv_rdy[0];
  // 1: input xbar config
  assign input_xbar_control_msg = router_msg[1][XBAR_CTRL_BITS-1:0];
  assign input_xbar_control_val = router_val[1];
  assign router_rdy[1] = input_xbar_control_rdy;
  // 2: classifier xbar inject
  assign classifier_xbar_recv_msg[0] = router_msg[2][DATA_BITS-1:0];
  assign classifier_xbar_recv_val[0] = router_val[2];
  assign router_rdy[2] = classifier_xbar_recv_rdy[0];
  // 3: classifier xbar config
  assign classifier_xbar_control_msg = router_msg[3][XBAR_CTRL_BITS-1:0];
  assign classifier_xbar_control_val = router_val[3];
  assign router_rdy[3] = classifier_xbar_control_rdy;
  // 4: output xbar inject
  // 1 bit here as the classifier output is 1 bit wide
  assign output_xbar_recv_msg[0] = router_msg[4][0];
  assign output_xbar_recv_val[0] = router_val[4];
  assign router_rdy[4] = output_xbar_recv_rdy[0];
  // 5: output xbar config
  assign output_xbar_control_msg = router_msg[5][XBAR_CTRL_BITS-1:0];
  assign output_xbar_control_val = router_val[5];
  assign router_rdy[5] = output_xbar_control_rdy;
  // 6: classifier cutoff freq
  assign classifier_config_msg[0] = router_msg[6][DATA_BITS-1:0];
  assign classifier_config_val[0] = router_val[6];
  assign router_rdy[6] = classifier_config_rdy[0];
  // 7: classifier cutoff mag
  assign classifier_config_msg[1] = router_msg[7][DATA_BITS-1:0];
  assign classifier_config_val[1] = router_val[7];
  assign router_rdy[7] = classifier_config_rdy[1];
  // 8: classifier sampling freq
  assign classifier_config_msg[2] = router_msg[8][DATA_BITS-1:0];
  assign classifier_config_val[2] = router_val[8];
  assign router_rdy[8] = classifier_config_rdy[2];
  // 9: loopback to arbiter
  assign arbiter_msg[9] = router_msg[9][DATA_BITS-1:0];
  assign arbiter_val[9] = router_val[9];
  assign router_rdy[9] = arbiter_rdy[9];
  // 10+: unused
  generate
    for (i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin : for_521 
      assign router_rdy[i] = 1'b0;
    end
  endgenerate

  // config messages for the classifiers shorter than 16 bits
  wire unused_xbar_cfg_bits = &{
    1'b0,
    router_msg[1][DATA_BITS-1:XBAR_CTRL_BITS],
    router_msg[3][DATA_BITS-1:XBAR_CTRL_BITS],
    router_msg[5][DATA_BITS-1:XBAR_CTRL_BITS],
    1'b0
  };
  // output xbar inject is 1 bit wide
  wire unused_output_xbar_msg = &{1'b0, router_msg[4][DATA_BITS-1:1], 1'b0};
  // address bits are retained by the router but we don't use them
  generate
    for (i = 0; i <= 9; i = i + 1) begin : for_538 
      wire unused_router_addr = &{1'b0, router_msg[i][DATA_BITS+ADDR_BITS-1:DATA_BITS], 1'b0};
    end
  endgenerate
  wire unused_router_val = &{1'b0, router_val[10:ROUTER_ARBITER_SIZE-1], 1'b0};
  wire unused_router_msg = &{1'b0, router_msg[10:ROUTER_ARBITER_SIZE-1], 1'b0};

  // 5 outputs:
  // 0: input xbar output
  assign arbiter_msg[0] = input_xbar_send_msg[0];
  assign arbiter_val[0] = input_xbar_send_val[0];
  assign input_xbar_send_rdy[0] = arbiter_rdy[0];
  // 1: unused
  assign arbiter_msg[1] = 16'b0;
  assign arbiter_val[1] = 1'b0;

  // 2: classifier xbar output
  assign arbiter_msg[2] = classifier_xbar_send_msg[0];
  assign arbiter_val[2] = classifier_xbar_send_val[0];
  assign classifier_xbar_send_rdy[0] = arbiter_rdy[2];
  // 3: unused
  assign arbiter_msg[3] = 16'b0;
  assign arbiter_val[3] = 1'b0;

  // 4: output xbar output
  // zero extend the classifier output to 16 bits
  assign arbiter_msg[4] = {15'b0, output_xbar_send_msg[0]};
  assign arbiter_val[4] = output_xbar_send_val[0];
  assign output_xbar_send_rdy[0] = arbiter_rdy[4];
  // 5-8: unused
  generate
    for (i = 5; i <= 8; i = i + 1) begin : for_569 
      assign arbiter_msg[i] = 16'b0;
      assign arbiter_val[i] = 1'b0;
    end
  endgenerate

  // 9: loopback to arbiter
  // 10+: unused
  generate
    for (i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin : for_578 
      assign arbiter_msg[i] = 16'b0;
      assign arbiter_val[i] = 1'b0;
    end
  endgenerate

  wire unused_arbiter_rdy = &{
    1'b0,
    arbiter_rdy[1],
    arbiter_rdy[3],
    arbiter_rdy[5:8],
    arbiter_rdy[10:ROUTER_ARBITER_SIZE-1],
    1'b0
  };

endmodule

/*
NOTE: Minion requires 4 cycles of delay between messages.
*/
module spi_Minion #(
  BIT_WIDTH = 32,
  N_SAMPLES = 8
) (
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   cs,
  input  logic                   sclk,
  input  logic                   mosi,
  output logic                   miso,
  input  logic [BIT_WIDTH - 1:0] recv_msg,
  output logic                   recv_rdy,
  input  logic                   recv_val,
  output logic [BIT_WIDTH - 1:0] send_msg,
  input  logic                   send_rdy,
  output logic                   send_val,
  output logic                   minion_parity,
  output logic                   adapter_parity
);

  logic                   push_en;
  logic                   pull_en;

  logic [BIT_WIDTH + 1:0] push_msg;
  logic [BIT_WIDTH - 1:0] pull_msg;
  logic                   pull_msg_val;
  logic                   pull_msg_spc;

  spi_helpers_Minion_PushPull #(
    .nbits(BIT_WIDTH + 2)
  ) minion (
    .clk(clk),
    .cs(cs),
    .miso(miso),
    .mosi(mosi),
    .reset(reset),
    .sclk(sclk),
    .pull_en(pull_en),
    .pull_msg({pull_msg_val, pull_msg_spc, pull_msg}),
    .push_en(push_en),
    .push_msg(push_msg),
    .parity(minion_parity)
  );

  spi_helpers_Minion_Adapter #(
    .nbits(BIT_WIDTH + 2),
    .num_entries(N_SAMPLES)
  ) adapter1 (
    .clk(clk),
    .reset(reset),
    .pull_en(pull_en),
    .pull_msg_val(pull_msg_val),
    .pull_msg_spc(pull_msg_spc),
    .pull_msg_data(pull_msg),
    .push_en(push_en),
    .push_msg_val_wrt(push_msg[BIT_WIDTH+1]),
    .push_msg_val_rd(push_msg[BIT_WIDTH]),
    .push_msg_data(push_msg[BIT_WIDTH-1:0]),
    .recv_msg(recv_msg),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),

    .send_msg(send_msg),
    .send_val(send_val),
    .send_rdy(send_rdy),
    .parity  (adapter_parity)
  );

endmodule
// ==========================================================================
// SPIMinionAdapterVRTL.v
// ==========================================================================
// An Adapter that converts push/pull interface from SPI to val/rdy interfaces. 

// Author : Kyle Infantino
// Date : Nov 30, 2021

`ifndef SPI_HELPERS_MINION_ADAPTER
`define SPI_HELPERS_MINION_ADAPTER


module spi_helpers_Minion_Adapter #(
  parameter int nbits = 8,
  parameter int num_entries = 1 
) (
  input  logic             clk,
  input  logic             reset,
  input  logic             pull_en,
  output logic             pull_msg_val,
  output logic             pull_msg_spc,
  output logic [nbits-3:0] pull_msg_data,
  input  logic             push_en,
  input  logic             push_msg_val_wrt,  // write mode
  input  logic             push_msg_val_rd,   // read mode
  input  logic [nbits-3:0] push_msg_data,
  input  logic [nbits-3:0] recv_msg,
  output logic             recv_rdy,
  input  logic             recv_val,
  output logic [nbits-3:0] send_msg,
  input  logic             send_rdy,
  output logic             send_val,
  output logic             parity
);

  logic                         open_entries;

  logic [            nbits-3:0] cm_q_send_msg;
  logic                         cm_q_send_rdy;
  logic                         cm_q_send_val;
  logic [$clog2(num_entries):0] unused;

  cmn_Queue #(4'b0, nbits - 2, num_entries) cm_q (
    .clk(clk),
    .num_free_entries(unused),
    .reset(reset),
    .enq_msg(recv_msg),
    .enq_rdy(recv_rdy),
    .enq_val(recv_val),
    .deq_msg(cm_q_send_msg),
    .deq_rdy(cm_q_send_rdy),
    .deq_val(cm_q_send_val)
  );

  logic [$clog2(num_entries):0] mc_q_num_free;
  logic                         mc_q_recv_rdy;
  logic                         mc_q_recv_val;

  cmn_Queue #(4'b0, nbits - 2, num_entries) mc_q (
    .clk(clk),
    .num_free_entries(mc_q_num_free),
    .reset(reset),
    .enq_msg(push_msg_data),
    .enq_rdy(mc_q_recv_rdy),
    .enq_val(mc_q_recv_val),
    .deq_msg(send_msg),
    .deq_rdy(send_rdy),
    .deq_val(send_val)
  );

  assign parity = (^send_msg) & send_val;

  always_comb begin : comb_block
    open_entries  = mc_q_num_free > 1;
    mc_q_recv_val = push_msg_val_wrt & push_en;
    pull_msg_spc  = mc_q_recv_rdy & ((~mc_q_recv_val) | open_entries);
    cm_q_send_rdy = push_msg_val_rd & pull_en;
    pull_msg_val  = cm_q_send_rdy & cm_q_send_val;
    pull_msg_data = cm_q_send_msg & {(nbits - 2) {pull_msg_val}};
  end

endmodule

`endif
//========================================================================
// Verilog Components: Queues
//========================================================================

`ifndef CMN_QUEUES_V
`define CMN_QUEUES_V


//------------------------------------------------------------------------
// Defines
//------------------------------------------------------------------------

`define CMN_QUEUE_NORMAL 4'b0000
`define CMN_QUEUE_PIPE 4'b0001
`define CMN_QUEUE_BYPASS 4'b0010

//------------------------------------------------------------------------
// Single-Element Queue Control Logic
//------------------------------------------------------------------------
// This is the control logic for a single-elment queue. It is designed to
// be attached to a storage element with a write enable. Additionally, it
// includes the ability to statically enable pipeline and/or bypass
// behavior. Pipeline behavior is when the deq_rdy signal is
// combinationally wired to the enq_rdy signal allowing elements to be
// dequeued and enqueued in the same cycle when the queue is full. Bypass
// behavior is when the enq_val signal is combinationally wired to the
// deq_val signal allowing elements to bypass the storage element if the
// storage element is empty.

module cmn_QueueCtrl1 #(
  parameter p_type = `CMN_QUEUE_NORMAL 
) (
  input logic clk,
  input logic reset,

  input  logic enq_val,  // Enqueue data is valid
  output logic enq_rdy,  // Ready for producer to do an enqueue

  output logic deq_val,  // Dequeue data is valid
  input  logic deq_rdy,  // Consumer is ready to do a dequeue

  output logic write_en,         // Write en signal to wire up to storage element
  output logic bypass_mux_sel,   // Used to control bypass mux for bypass queues
  output logic num_free_entries  // Either zero or one
);

  // Status register

  logic full;
  logic full_next;

  always_ff @(posedge clk) begin
    full <= reset ? 1'b0 : full_next;
  end

  assign num_free_entries = full ? 1'b0 : 1'b1;

  // Determine if pipeline or bypass behavior is enabled

  localparam c_pipe_en = |(p_type & `CMN_QUEUE_PIPE);
  localparam c_bypass_en = |(p_type & `CMN_QUEUE_BYPASS);

  // We enq/deq only when they are both ready and valid

  logic do_enq;
  assign do_enq = enq_rdy && enq_val;

  logic do_deq;
  assign do_deq = deq_rdy && deq_val;

  // Determine if we have pipeline or bypass behaviour and
  // set the write enable accordingly.

  logic empty;
  assign empty = ~full;

  logic do_pipe;
  assign do_pipe = c_pipe_en && full && do_enq && do_deq;

  logic do_bypass;
  assign do_bypass      = c_bypass_en && empty && do_enq && do_deq;

  assign write_en       = do_enq && ~do_bypass;

  // Regardless of the type of queue or whether or not we are actually
  // doing a bypass, if the queue is empty then we select the enq bits,
  // otherwise we select the output of the queue state elements.

  assign bypass_mux_sel = empty;

  // Ready signals are calculated from full register. If pipeline
  // behavior is enabled, then the enq_rdy signal is also calculated
  // combinationally from the deq_rdy signal. If bypass behavior is
  // enabled then the deq_val signal is also calculated combinationally
  // from the enq_val signal.

  assign enq_rdy        = ~full || (c_pipe_en && full && deq_rdy);
  assign deq_val        = ~empty || (c_bypass_en && empty && enq_val);

  // Control logic for the full register input

  assign full_next      = (do_deq && ~do_pipe) ? 1'b0 : (do_enq && ~do_bypass) ? 1'b1 : full;

endmodule

//------------------------------------------------------------------------
// Single-Element Queue Datapath
//------------------------------------------------------------------------
// This is the datpath for single element queues. It includes a register
// and a bypass mux if needed.

module cmn_QueueDpath1 #(
  parameter p_type      = `CMN_QUEUE_NORMAL,
  parameter p_msg_nbits = 1 
) (
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   write_en,
  input  logic                   bypass_mux_sel,
  input  logic [p_msg_nbits-1:0] enq_msg,
  output logic [p_msg_nbits-1:0] deq_msg
);

  // Queue storage

  logic [p_msg_nbits-1:0] qstore;

  cmn_EnResetReg #(p_msg_nbits) qstore_reg (
    .clk  (clk),
    .reset(reset),
    .en   (write_en),
    .d    (enq_msg),
    .q    (qstore)
  );

  // Bypass muxing

  generate
    if (|(p_type & `CMN_QUEUE_BYPASS))

      cmn_Mux2 #(p_msg_nbits) bypass_mux (
        .in0(qstore),
        .in1(enq_msg),
        .sel(bypass_mux_sel),
        .out(deq_msg)
      );

    else begin
      logic unused = &{1'b0, bypass_mux_sel, 1'b0};
      assign deq_msg = qstore;
    end
  endgenerate

endmodule

//------------------------------------------------------------------------
// Multi-Element Queue Control Logic
//------------------------------------------------------------------------
// This is the control logic for a multi-elment queue. It is designed to
// be attached to a Regfile storage element. Additionally, it includes
// the ability to statically enable pipeline and/or bypass behavior.
// Pipeline behavior is when the deq_rdy signal is combinationally wired
// to the enq_rdy signal allowing elements to be dequeued and enqueued in
// the same cycle when the queue is full. Bypass behavior is when the
// enq_val signal is cominationally wired to the deq_val signal allowing
// elements to bypass the storage element if the storage element is
// empty.

module cmn_QueueCtrl #(
  parameter p_type     = `CMN_QUEUE_NORMAL,
  parameter p_num_msgs = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_msgs) 
) (
  input logic clk,
  reset,

  input  logic enq_val,  // Enqueue data is valid
  output logic enq_rdy,  // Ready for producer to enqueue

  output logic deq_val,  // Dequeue data is valid
  input  logic deq_rdy,  // Consumer is ready to dequeue

  output logic                    write_en,         // Wen to wire to regfile
  output logic [c_addr_nbits-1:0] write_addr,       // Waddr to wire to regfile
  output logic [c_addr_nbits-1:0] read_addr,        // Raddr to wire to regfile
  output logic                    bypass_mux_sel,   // Control mux for bypass queues
  output logic [  c_addr_nbits:0] num_free_entries  // Num of free entries in queue
);

  // Enqueue and dequeue pointers

  logic [c_addr_nbits-1:0] enq_ptr;
  logic [c_addr_nbits-1:0] enq_ptr_next;

  cmn_ResetReg #(c_addr_nbits) enq_ptr_reg (
    .clk  (clk),
    .reset(reset),
    .d    (enq_ptr_next),
    .q    (enq_ptr)
  );

  logic [c_addr_nbits-1:0] deq_ptr;
  logic [c_addr_nbits-1:0] deq_ptr_next;

  cmn_ResetReg #(c_addr_nbits) deq_ptr_reg (
    .clk  (clk),
    .reset(reset),
    .d    (deq_ptr_next),
    .q    (deq_ptr)
  );

  assign write_addr = enq_ptr;
  assign read_addr  = deq_ptr;

  // Extra state to tell difference between full and empty

  logic full;
  logic full_next;

  cmn_ResetReg #(1) full_reg (
    .clk  (clk),
    .reset(reset),
    .d    (full_next),
    .q    (full)
  );

  // Determine if pipeline or bypass behavior is enabled

  localparam c_pipe_en = |(p_type & `CMN_QUEUE_PIPE);
  localparam c_bypass_en = |(p_type & `CMN_QUEUE_BYPASS);

  // We enq/deq only when they are both ready and valid

  logic do_enq;
  assign do_enq = enq_rdy && enq_val;

  logic do_deq;
  assign do_deq = deq_rdy && deq_val;

  // Determine if we have pipeline or bypass behaviour and
  // set the write enable accordingly.

  logic empty;
  assign empty = ~full && (enq_ptr == deq_ptr);

  logic do_pipe;
  assign do_pipe = c_pipe_en && full && do_enq && do_deq;

  logic do_bypass;
  assign do_bypass = c_bypass_en && empty && do_enq && do_deq;

  assign write_en = do_enq && ~do_bypass;

  // Regardless of the type of queue or whether or not we are actually
  // doing a bypass, if the queue is empty then we select the enq bits,
  // otherwise we select the output of the queue state elements.

  assign bypass_mux_sel = empty;

  // Ready signals are calculated from full register. If pipeline
  // behavior is enabled, then the enq_rdy signal is also calculated
  // combinationally from the deq_rdy signal. If bypass behavior is
  // enabled then the deq_val signal is also calculated combinationally
  // from the enq_val signal.

  assign enq_rdy = ~full || (c_pipe_en && full && deq_rdy);
  assign deq_val = ~empty || (c_bypass_en && empty && enq_val);

  // Control logic for the enq/deq pointers and full register

  logic [c_addr_nbits-1:0] deq_ptr_plus1;
  assign deq_ptr_plus1 = deq_ptr + 1'b1;

  /* verilator lint_off WIDTH */

  logic [c_addr_nbits-1:0] deq_ptr_inc;
  assign deq_ptr_inc = (deq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : deq_ptr_plus1;

  logic [c_addr_nbits-1:0] enq_ptr_plus1;
  assign enq_ptr_plus1 = enq_ptr + 1'b1;

  logic [c_addr_nbits-1:0] enq_ptr_inc;
  assign enq_ptr_inc = (enq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : enq_ptr_plus1;

  /* verilator lint_on WIDTH */

  assign deq_ptr_next = (do_deq && ~do_bypass) ? (deq_ptr_inc) : deq_ptr;

  assign enq_ptr_next = (do_enq && ~do_bypass) ? (enq_ptr_inc) : enq_ptr;

  assign full_next
    = ( do_enq && ~do_deq && ( enq_ptr_inc == deq_ptr ) ) ? 1'b1
    : ( do_deq && full && ~do_pipe )                      ? 1'b0
    :                                                       full;

  // Number of free entries

  assign num_free_entries
    = full                ? {(c_addr_nbits+1){1'b0}}
    : empty               ? p_num_msgs[c_addr_nbits:0]
    : (enq_ptr > deq_ptr) ? p_num_msgs[c_addr_nbits:0] - (enq_ptr - deq_ptr)
    : (deq_ptr > enq_ptr) ? deq_ptr - enq_ptr
    :                       {(c_addr_nbits+1){1'bx}};

endmodule

//------------------------------------------------------------------------
// Multi-Element Queue Datapath
//------------------------------------------------------------------------
// This is the datpath for multi-element queues. It includes a register
// and a bypass mux if needed.

module cmn_QueueDpath #(
  parameter p_type      = `CMN_QUEUE_NORMAL,
  parameter p_msg_nbits = 4,
  parameter p_num_msgs  = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_msgs) 
) (
  input  logic                    clk,
  input  logic                    write_en,
  input  logic                    bypass_mux_sel,
  input  logic [c_addr_nbits-1:0] write_addr,
  input  logic [c_addr_nbits-1:0] read_addr,
  input  logic [ p_msg_nbits-1:0] enq_msg,
  output logic [ p_msg_nbits-1:0] deq_msg
);

  // Queue storage

  logic [p_msg_nbits-1:0] read_data;

  cmn_Regfile_1r1w #(p_msg_nbits, p_num_msgs) qstore (
    .clk       (clk),
    .read_addr (read_addr),
    .read_data (read_data),
    .write_en  (write_en),
    .write_addr(write_addr),
    .write_data(enq_msg)
  );

  // Bypass muxing

  generate
    if (|(p_type & `CMN_QUEUE_BYPASS))

      cmn_Mux2 #(p_msg_nbits) bypass_mux (
        .in0(read_data),
        .in1(enq_msg),
        .sel(bypass_mux_sel),
        .out(deq_msg)
      );

    else begin
      logic unused = 1'b0 & bypass_mux_sel;
      assign deq_msg = read_data;
    end
  endgenerate

endmodule

//------------------------------------------------------------------------
// Queue
//------------------------------------------------------------------------

module cmn_Queue #(
  parameter p_type      = `CMN_QUEUE_NORMAL,
  parameter p_msg_nbits = 1,
  parameter p_num_msgs  = 2,

  // parameters not meant to be set outside this module
  parameter c_addr_nbits = $clog2(p_num_msgs) 
) (
  input logic clk,
  input logic reset,

  input  logic                   enq_val,
  output logic                   enq_rdy,
  input  logic [p_msg_nbits-1:0] enq_msg,

  output logic                   deq_val,
  input  logic                   deq_rdy,
  output logic [p_msg_nbits-1:0] deq_msg,

  output logic [c_addr_nbits:0] num_free_entries
);

  generate
    if (p_num_msgs == 1) begin

      logic write_en;
      logic bypass_mux_sel;

      cmn_QueueCtrl1 #(p_type) ctrl (
        .clk             (clk),
        .reset           (reset),
        .enq_val         (enq_val),
        .enq_rdy         (enq_rdy),
        .deq_val         (deq_val),
        .deq_rdy         (deq_rdy),
        .write_en        (write_en),
        .bypass_mux_sel  (bypass_mux_sel),
        .num_free_entries(num_free_entries)
      );

      cmn_QueueDpath1 #(p_type, p_msg_nbits) dpath (
        .clk           (clk),
        .reset         (reset),
        .write_en      (write_en),
        .bypass_mux_sel(bypass_mux_sel),
        .enq_msg       (enq_msg),
        .deq_msg       (deq_msg)
      );

    end else begin

      logic                    write_en;
      logic                    bypass_mux_sel;
      logic [c_addr_nbits-1:0] write_addr;
      logic [c_addr_nbits-1:0] read_addr;

      cmn_QueueCtrl #(p_type, p_num_msgs) ctrl (
        .clk             (clk),
        .reset           (reset),
        .enq_val         (enq_val),
        .enq_rdy         (enq_rdy),
        .deq_val         (deq_val),
        .deq_rdy         (deq_rdy),
        .write_en        (write_en),
        .write_addr      (write_addr),
        .read_addr       (read_addr),
        .bypass_mux_sel  (bypass_mux_sel),
        .num_free_entries(num_free_entries)
      );

      cmn_QueueDpath #(p_type, p_msg_nbits, p_num_msgs) dpath (
        .clk           (clk),
        .write_en      (write_en),
        .bypass_mux_sel(bypass_mux_sel),
        .write_addr    (write_addr),
        .read_addr     (read_addr),
        .enq_msg       (enq_msg),
        .deq_msg       (deq_msg)
      );

    end
  endgenerate

  // Assertions

  /*
  always_ff @( posedge clk ) begin
    if ( !reset ) begin
      `CMN_ASSERT_NOT_X( enq_val );
      `CMN_ASSERT_NOT_X( enq_rdy );
      `CMN_ASSERT_NOT_X( deq_val );
      `CMN_ASSERT_NOT_X( deq_rdy );
    end
  end
  */

  // Line Tracing

  //  logic [`CMN_TRACE_NBITS_TO_NCHARS(p_msg_nbits)*8-1:0] str;
  //
  //  `CMN_TRACE_BEGIN
  //  begin
  //
  //    $sformat( str, "%x", enq_msg );
  //    cmn_trace.append_val_rdy_str( trace_str, enq_val, enq_rdy, str );
  //
  //    cmn_trace.append_str( trace_str, "(" );
  //    $sformat( str, "%x", p_num_msgs-num_free_entries );
  //    cmn_trace.append_str( trace_str, str );
  //    cmn_trace.append_str( trace_str, ")" );
  //
  //    $sformat( str, "%x", deq_msg );
  //    cmn_trace.append_val_rdy_str( trace_str, deq_val, deq_rdy, str );

  // end
  // endtask

endmodule

`endif  /* CMN_QUEUES_V */

//========================================================================
// Verilog Components: Registers
//========================================================================

// Note that we place the register output earlier in the port list since
// this is one place we might actually want to use positional port
// binding like this:
//
//  logic [p_nbits-1:0] result_B;
//  cmn_Reg#(p_nbits) result_AB( clk, result_B, result_A );

`ifndef CMN_REGS_V
`define CMN_REGS_V


//------------------------------------------------------------------------
// Postive-edge triggered flip-flop
//------------------------------------------------------------------------

module cmn_Reg #(
  parameter p_nbits = 1 
) (
  input  logic               clk,  // Clock input
  output logic [p_nbits-1:0] q,    // Data output
  input  logic [p_nbits-1:0] d     // Data input
);

  always_ff @(posedge clk) q <= d;

endmodule

//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with reset
//------------------------------------------------------------------------

module cmn_ResetReg #(
  parameter p_nbits       = 1,
  parameter p_reset_value = 0 
) (
  input  logic               clk,    // Clock input
  input  logic               reset,  // Sync reset input
  output logic [p_nbits-1:0] q,      // Data output
  input  logic [p_nbits-1:0] d       // Data input
);

  always_ff @(posedge clk) q <= reset ? p_reset_value : d;

endmodule

//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with enable
//------------------------------------------------------------------------

module cmn_EnReg #(
  parameter p_nbits = 1 
) (
  input  logic               clk,  // Clock input
  output logic [p_nbits-1:0] q,    // Data output
  input  logic [p_nbits-1:0] d,    // Data input
  input  logic               en    // Enable input
);

  always_ff @(posedge clk) if (en) q <= d;

endmodule

//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with enable and reset
//------------------------------------------------------------------------

module cmn_EnResetReg #(
  parameter p_nbits       = 1,
  parameter p_reset_value = 0 
) (
  input  logic               clk,    // Clock input
  input  logic               reset,  // Sync reset input
  output logic [p_nbits-1:0] q,      // Data output
  input  logic [p_nbits-1:0] d,      // Data input
  input  logic               en      // Enable input
);

  always_ff @(posedge clk) if (reset || en) q <= reset ? p_nbits'(p_reset_value) : d;

endmodule

`endif  /* CMN_REGS_V */

//========================================================================
// vc-Assert
//========================================================================

`ifndef CMN_ASSERT_V
`define CMN_ASSERT_V

//------------------------------------------------------------------------
// CMN_PROPAGATE_X
//------------------------------------------------------------------------

`define CMN_PROPAGATE_X(i_, o_)                                        \
  if ((|(i_ ^ i_)) == 1'b0);                                            \
  else                                                                  \
    o_ = o_ + 1'bx

//------------------------------------------------------------------------
// CMN_ASSERT
//------------------------------------------------------------------------

`define CMN_ASSERT(expr_)                                              \
  if ( expr_ );                                                         \
  else begin                                                            \
    $display( "\n CMN_ASSERT FAILED\n  - assertion       :%s\n  - module instance : %m\n  - time            : %0d\n", \
              "expr_", $time );                                         \
    $finish;                                                            \
  end                                                                   \
  if (1)

//------------------------------------------------------------------------
// CMN_ASSERT_FAIL
//------------------------------------------------------------------------

`define CMN_ASSERT_FAIL(msg_)                                         \
  $display( "\n CMN_ASSERT FAILED\n  - assertion       :%s\n  - module instance : %m\n  - time            : %0d\n", \
            msg_, $time );                                             \
  $finish;                                                             \
  if (1)

//------------------------------------------------------------------------
// CMN_ASSERT_NOT_X
//------------------------------------------------------------------------

`define CMN_ASSERT_NOT_X(net_)                                         \
  if ((|(net_ ^ net_)) == 1'b0);                                        \
  else begin                                                            \
    $display( "\n CMN_ASSERT FAILED\n  - assertion that net not contain X's failed\n  - module instance : %m\n  - net             :%s\n  - time            : %0d\n", \
              "net_", $time );                                          \
    $finish;                                                            \
  end                                                                   \
  if (1)

`endif  /* CMN_ASSERT_V */

//========================================================================
// Verilog Components: Muxes
//========================================================================

`ifndef CMN_MUXES_V
`define CMN_MUXES_V

//------------------------------------------------------------------------
// 2 Input Mux
//------------------------------------------------------------------------

module cmn_Mux2 #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  input  logic               sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      1'd0: out = in0;
      1'd1: out = in1;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 3 Input Mux
//------------------------------------------------------------------------

module cmn_Mux3 #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  input  logic [        1:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      2'd0: out = in0;
      2'd1: out = in1;
      2'd2: out = in2;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 4 Input Mux
//------------------------------------------------------------------------

module cmn_Mux4 #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  input  logic [        1:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      2'd0: out = in0;
      2'd1: out = in1;
      2'd2: out = in2;
      2'd3: out = in3;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 5 Input Mux
//------------------------------------------------------------------------

module cmn_Mux5 #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 6 Input Mux
//------------------------------------------------------------------------

module cmn_Mux6 #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 7 Input Mux
//------------------------------------------------------------------------

module cmn_Mux7 #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  in6,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      3'd6: out = in6;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 8 Input Mux
//------------------------------------------------------------------------

module cmn_Mux8 #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  in6,
  in7,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      3'd6: out = in6;
      3'd7: out = in7;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// N Input Mux
//------------------------------------------------------------------------

module cmn_MuxN
#(
  parameter nbits = 1,
  parameter ninputs = 2
)(
  input  logic               [nbits-1:0]   in   [0:ninputs-1], 
  input  logic     [$clog2(ninputs)-1:0]   sel,
  output logic               [nbits-1:0]   out
);

  assign out = in[sel];

endmodule

`endif /* CMN_MUXES_V */

//========================================================================
// Verilog Components: Register Files
//========================================================================

`ifndef CMN_REGFILES_V
`define CMN_REGFILES_V


//------------------------------------------------------------------------
// 1r1w register file
//------------------------------------------------------------------------

module cmn_Regfile_1r1w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_entries) 
) (
  input logic clk,

  // Read port (combinational read)

  input  logic [c_addr_nbits-1:0] read_addr,
  output logic [p_data_nbits-1:0] read_data,

  // Write port (sampled on the rising clock edge)

  input logic                    write_en,
  input logic [c_addr_nbits-1:0] write_addr,
  input logic [p_data_nbits-1:0] write_data
);

  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

  // Combinational read

  assign read_data = rfile[read_addr];

  // Write on positive clock edge

  always_ff @(posedge clk) if (write_en) rfile[write_addr] <= write_data;

  // Assertions

  /*
  always_ff @( posedge clk ) begin
    if ( !reset ) begin
      `CMN_ASSERT_NOT_X( write_en );

      // If write_en is one, then write address better be less than the
      // number of entries and definitely cannot be X's.

      if ( write_en ) begin
        `CMN_ASSERT_NOT_X( write_addr );
        `CMN_ASSERT( write_addr < p_num_entries );
      end

    end
  end
  */

endmodule

//------------------------------------------------------------------------
// 1r1w register file with reset
//------------------------------------------------------------------------

module cmn_ResetRegfile_1r1w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,
  parameter p_reset_value = 0,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_entries) 
) (
  input logic clk,
  input logic reset,

  // Read port (combinational read)

  input  logic [c_addr_nbits-1:0] read_addr,
  output logic [p_data_nbits-1:0] read_data,

  // Write port (sampled on the rising clock edge)

  input logic                    write_en,
  input logic [c_addr_nbits-1:0] write_addr,
  input logic [p_data_nbits-1:0] write_data
);

  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

  // Combinational read

  assign read_data = rfile[read_addr];

  // Write on positive clock edge. We have to use a generate statement to
  // allow us to include the reset logic for each individual register.

  genvar i;
  generate
    for (i = 0; i < p_num_entries; i = i + 1) begin : wport
      always_ff @(posedge clk)
        if (reset) rfile[i] <= p_reset_value;
        else if (write_en && (i[c_addr_nbits-1:0] == write_addr)) rfile[i] <= write_data;
    end
  endgenerate

  // Assertions

  /*
  always_ff @( posedge clk ) begin
    if ( !reset ) begin
      `CMN_ASSERT_NOT_X( write_en );

      // If write_en is one, then write address better be less than the
      // number of entries and definitely cannot be X's.

      if ( write_en ) begin
        `CMN_ASSERT_NOT_X( write_addr );
        `CMN_ASSERT( write_addr < p_num_entries );
      end

    end
  end
  */

endmodule

//------------------------------------------------------------------------
// 2r1w register file
//------------------------------------------------------------------------

module cmn_Regfile_2r1w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_entries) 
) (
  input logic clk,

  // Read port 0 (combinational read)

  input  logic [c_addr_nbits-1:0] read_addr0,
  output logic [p_data_nbits-1:0] read_data0,

  // Read port 1 (combinational read)

  input  logic [c_addr_nbits-1:0] read_addr1,
  output logic [p_data_nbits-1:0] read_data1,

  // Write port (sampled on the rising clock edge)

  input logic                    write_en,
  input logic [c_addr_nbits-1:0] write_addr,
  input logic [p_data_nbits-1:0] write_data
);

  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

  // Combinational read

  assign read_data0 = rfile[read_addr0];
  assign read_data1 = rfile[read_addr1];

  // Write on positive clock edge

  always_ff @(posedge clk) if (write_en) rfile[write_addr] <= write_data;

  // Assertions

  /*
  always_ff @( posedge clk ) begin
    if ( !reset ) begin
      `CMN_ASSERT_NOT_X( write_en );

      // If write_en is one, then write address better be less than the
      // number of entries and definitely cannot be X's.

      if ( write_en ) begin
        `CMN_ASSERT_NOT_X( write_addr );
        `CMN_ASSERT( write_addr < p_num_entries );
      end

    end
  end
  */

endmodule

//------------------------------------------------------------------------
// 2r2w register file
//------------------------------------------------------------------------

module cmn_Regfile_2r2w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_entries) 
) (
  input logic clk,

  // Read port 0 (combinational read)

  input  logic [c_addr_nbits-1:0] read_addr0,
  output logic [p_data_nbits-1:0] read_data0,

  // Read port 1 (combinational read)

  input  logic [c_addr_nbits-1:0] read_addr1,
  output logic [p_data_nbits-1:0] read_data1,

  // Write port (sampled on the rising clock edge)

  input logic                    write_en0,
  input logic [c_addr_nbits-1:0] write_addr0,
  input logic [p_data_nbits-1:0] write_data0,

  // Write port (sampled on the rising clock edge)

  input logic                    write_en1,
  input logic [c_addr_nbits-1:0] write_addr1,
  input logic [p_data_nbits-1:0] write_data1
);

  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

  // Combinational read

  assign read_data0 = rfile[read_addr0];
  assign read_data1 = rfile[read_addr1];

  // Write on positive clock edge

  always_ff @(posedge clk) begin

    if (write_en0) rfile[write_addr0] <= write_data0;

    if (write_en1) rfile[write_addr1] <= write_data1;

  end

  // Assertions

  /*
  always_ff @( posedge clk ) begin
    if ( !reset ) begin
      `CMN_ASSERT_NOT_X( write_en0 );
      `CMN_ASSERT_NOT_X( write_en1 );

      // If write_en is one, then write address better be less than the
      // number of entries and definitely cannot be X's.

      if ( write_en0 ) begin
        `CMN_ASSERT_NOT_X( write_addr0 );
        `CMN_ASSERT( write_addr0 < p_num_entries );
      end

      if ( write_en1 ) begin
        `CMN_ASSERT_NOT_X( write_addr1 );
        `CMN_ASSERT( write_addr1 < p_num_entries );
      end

      // It is invalid to use the same write address for both write ports

      if ( write_en0 && write_en1 ) begin
        `CMN_ASSERT( write_addr0 != write_addr1 );
      end

    end
  end
  */

endmodule

//------------------------------------------------------------------------
// Register file specialized for r0 == 0
//------------------------------------------------------------------------

module cmn_Regfile_2r1w_zero (
  input logic clk,

  input  logic [ 4:0] rd_addr0,
  output logic [31:0] rd_data0,

  input  logic [ 4:0] rd_addr1,
  output logic [31:0] rd_data1,

  input logic        wr_en,
  input logic [ 4:0] wr_addr,
  input logic [31:0] wr_data
);

  // these wires are to be hooked up to the actual register file read
  // ports

  logic [31:0] rf_read_data0;
  logic [31:0] rf_read_data1;

  cmn_Regfile_2r1w #(
    .p_data_nbits (32),
    .p_num_entries(32)
  ) r_file (
    .clk       (clk),
    .read_addr0(rd_addr0),
    .read_data0(rf_read_data0),
    .read_addr1(rd_addr1),
    .read_data1(rf_read_data1),
    .write_en  (wr_en),
    .write_addr(wr_addr),
    .write_data(wr_data)
  );

  // we pick 0 value when either read address is 0
  assign rd_data0 = (rd_addr0 == 5'd0) ? 32'd0 : rf_read_data0;
  assign rd_data1 = (rd_addr1 == 5'd0) ? 32'd0 : rf_read_data1;

endmodule

`endif  /* CMN_REGFILES_V */

// ==========================================================================
// SPIMinionVRTL.v
// ==========================================================================
// SPIMinion module. Supports SPI mode 0
// Uses a push/pull interface.

// Author : Yanghui Ou, Modified by Kyle Infantino

`ifndef SPI_HELPERS_MINION_PUSHPULL
`define SPI_HELPERS_MINION_PUSHPULL


module spi_helpers_Minion_PushPull #(
  parameter int nbits = 8 
) (
  input  logic             clk,
  input  logic             cs,
  output logic             miso,
  input  logic             mosi,
  input  logic             reset,
  input  logic             sclk,
  output logic             pull_en,
  input  logic [nbits-1:0] pull_msg,
  output logic             push_en,
  output logic [nbits-1:0] push_msg,
  output logic             parity
);
  //-------------------------------------------------------------
  // Component cs_sync
  //-------------------------------------------------------------

  logic cs_sync_clk;
  logic cs_sync_in_;
  logic cs_sync_negedge_;
  logic cs_sync_out;
  logic cs_sync_posedge_;
  logic cs_sync_reset;

  spi_helpers_Synchronizer #(1'b1) cs_sync (
    .clk(cs_sync_clk),
    .in_(cs_sync_in_),
    .negedge_(cs_sync_negedge_),
    .out(cs_sync_out),
    .posedge_(cs_sync_posedge_),
    .reset(cs_sync_reset)
  );

  //-------------------------------------------------------------
  // Component mosi_sync
  //-------------------------------------------------------------

  logic mosi_sync_clk;
  logic mosi_sync_in_;
  logic mosi_sync_out;
  logic mosi_sync_negedge_;  // not used
  logic mosi_sync_posedge_;  // not used
  logic mosi_sync_reset;

  spi_helpers_Synchronizer #(1'b0) mosi_sync (
    .clk(mosi_sync_clk),
    .in_(mosi_sync_in_),
    .negedge_(mosi_sync_negedge_),
    .out(mosi_sync_out),
    .posedge_(mosi_sync_posedge_),
    .reset(mosi_sync_reset)
  );

  //-------------------------------------------------------------
  // Component sclk_sync
  //-------------------------------------------------------------

  logic sclk_sync_clk;
  logic sclk_sync_in_;
  logic sclk_sync_negedge_;
  logic sclk_sync_out;  // not used
  logic sclk_sync_posedge_;
  logic sclk_sync_reset;

  spi_helpers_Synchronizer #(1'b0) sclk_sync (
    .clk(sclk_sync_clk),
    .in_(sclk_sync_in_),
    .negedge_(sclk_sync_negedge_),
    .out(sclk_sync_out),
    .posedge_(sclk_sync_posedge_),
    .reset(sclk_sync_reset)
  );

  //-------------------------------------------------------------
  // Component shreg_in
  //-------------------------------------------------------------

  logic             shreg_in_clk;
  logic             shreg_in_in_;
  logic [nbits-1:0] shreg_in_load_data;
  logic             shreg_in_load_en;
  logic [nbits-1:0] shreg_in_out;
  logic             shreg_in_reset;
  logic             shreg_in_shift_en;

  regs_shift_Bitwise #(nbits) shreg_in (
    .clk(shreg_in_clk),
    .reset(shreg_in_reset),
    .d(shreg_in_in_),
    .en(shreg_in_shift_en),
    .load(shreg_in_load_data),
    .load_en(shreg_in_load_en),
    .q(shreg_in_out)
  );

  //-------------------------------------------------------------
  // Component shreg_out
  //-------------------------------------------------------------

  logic             shreg_out_clk;
  logic             shreg_out_in_;
  logic [nbits-1:0] shreg_out_load_data;
  logic             shreg_out_load_en;
  logic [nbits-1:0] shreg_out_out;
  logic             shreg_out_reset;
  logic             shreg_out_shift_en;

  regs_shift_Bitwise #(nbits) shreg_out (
    .clk(shreg_out_clk),
    .reset(shreg_out_reset),
    .d(shreg_out_in_),
    .en(shreg_out_shift_en),
    .load(shreg_out_load_data),
    .load_en(shreg_out_load_en),
    .q(shreg_out_out)
  );

  always_comb begin
    shreg_in_shift_en  = (~cs_sync_out) & sclk_sync_posedge_;
    shreg_out_shift_en = (~cs_sync_out) & sclk_sync_negedge_;
  end

  assign cs_sync_clk         = clk;
  assign cs_sync_reset       = reset;
  assign cs_sync_in_         = cs;
  assign sclk_sync_clk       = clk;
  assign sclk_sync_reset     = reset;
  assign sclk_sync_in_       = sclk;
  assign mosi_sync_clk       = clk;
  assign mosi_sync_reset     = reset;
  assign mosi_sync_in_       = mosi;
  assign shreg_in_clk        = clk;
  assign shreg_in_reset      = reset;
  assign shreg_in_in_        = mosi_sync_out;
  assign shreg_in_load_en    = 1'b0;
  assign shreg_in_load_data  = {nbits{1'b0}};
  assign shreg_out_clk       = clk;
  assign shreg_out_reset     = reset;
  assign shreg_out_in_       = 1'b0;
  assign shreg_out_load_en   = pull_en;
  assign shreg_out_load_data = pull_msg;
  assign miso                = shreg_out_out[nbits-1];
  assign pull_en             = cs_sync_negedge_;
  assign push_en             = cs_sync_posedge_;
  assign push_msg            = shreg_in_out;
  assign parity              = (^push_msg[nbits-3:0]) & push_en;


  // unused net
  logic unused;
  assign unused = &{1'b0, mosi_sync_negedge_, mosi_sync_posedge_, sclk_sync_out, 1'b0};

endmodule

`endif  /* SPI_HELPERS_MINION_PUSHPULL */

`ifndef REGS_SHIFT_BITWISE
`define REGS_SHIFT_BITWISE
//------------------------------------------------------------------------
// N-bit bitwise shift register
//------------------------------------------------------------------------
/*
This is a shift register storing `nbits` total bits.

One bit of data can be inputted per clock cycle, gated by the `en` input.
The entire register will be shifted to the left by one bit when this happens.

For example, here is a simulation of a 4 bit register:
```
reset held high
  0000
en high, d = 1
  0001
en high, d = 0
  0010
load_en high, load = 1111
  1111
```

The entire register can be overridden by the `load` input when `load_en` is high.
Data cannot be inputted when `load_en` is high.
*/
module regs_shift_Bitwise #(
  parameter int p_nbits = 8,
  parameter bit p_reset_value = 0 
) (
  input  logic               clk,      // Clock input
  input  logic               reset,    // Sync reset input
  input  logic               d,        // One bit data input
  input  logic               en,       // Enable input
  input  logic [p_nbits-1:0] load,     // Directly load data input
  input  logic               load_en,  // Enable load
  output logic [p_nbits-1:0] q         // Data output
);

  always_ff @(posedge clk) begin
    if (reset) begin
      q <= {p_nbits{p_reset_value}};
    end else if (load_en) begin
      q <= load;
    end else if ((~load_en) & en) begin
      q <= {q[p_nbits-2:0], d};
    end else begin
      q <= q;
    end
  end
endmodule

`endif
/*
==========================================================================
Synchronizer.v
==========================================================================
 - RTL code for the Synchronizer module.
 - It samples the input signal using the device clock and also detects
     positive and negative edges.
 - Reference: https://www.fpga4fun.com/SPI2.html
*/

`ifndef SPI_HELPERS_SYNCHRONIZER
`define SPI_HELPERS_SYNCHRONIZER

module spi_helpers_Synchronizer #(
  parameter bit reset_value = 0 
) (
  input  logic clk,
  input  logic reset,
  input  logic in_,
  output logic posedge_,
  output logic negedge_,
  output logic out
);
  logic [2:0] shreg;  // Clock value history

  always_comb begin
    posedge_ = (~shreg[2]) & shreg[1];  // Low to high transition
    negedge_ = shreg[2] & (~shreg[1]);  // High to low transition
  end

  always_ff @(posedge clk) begin
    if (reset) begin
      shreg <= {3{reset_value}};
    end else shreg <= {shreg[1:0], in_};
  end

  assign out = shreg[1];

endmodule

`endif
`ifndef arbiter_router_ROUTER
`define arbiter_router_ROUTER

/*
  * Module: Router
  *
  * Functionality: The router takes in an n-bit long message, and uses the first log2(number of outputs) of the input
  * to determine which receiving port receives a high valid bit. All receiving ports receive the input but not a 
  * corresponding high valid bit. The block itself outputs a low ready bit if its internal queue is full;
  * otherwise the ready bit is high.
  * 
  * NOTE: Address bits are not truncated from the input message.
  *
  * Dependencies: muxes.v, demuxes.v, queues.v
  * @param nbits: number of total bits in the message (includes address bits)
  * @param noutputs: number of output ports
*/
module arbiter_router_Router #(
  parameter int nbits = 32,
  parameter int noutputs = 8 
) (
  input logic clk,
  input logic reset,

  // In stream
  input  logic             istream_val,
  input  logic [nbits-1:0] istream_msg,
  output logic             istream_rdy,

  // Out stream
  output logic             ostream_val[noutputs],
  output logic [nbits-1:0] ostream_msg[noutputs],
  input  logic             ostream_rdy[noutputs]
);
  // Number of address bits
  localparam int n_addr_bits = $clog2(noutputs);

  logic [n_addr_bits-1:0] select;
  logic [      nbits-1:0] payload_msg;
  logic                   payload_val;
  logic                   payload_rdy;

  assign select = payload_msg[nbits-1 : nbits-n_addr_bits];

  // not used, assigned to the unused net below
  logic [$clog2(3):0] num_free_entries;

  cmn_Queue #(
    .p_msg_nbits(nbits),
    .p_num_msgs (3)
  ) queue_inst (
    .clk             (clk),
    .reset           (reset),
    .enq_val         (istream_val),
    .enq_rdy         (istream_rdy),
    .enq_msg         (istream_msg),
    .deq_val         (payload_val),
    .deq_rdy         (payload_rdy),
    .deq_msg         (payload_msg),
    .num_free_entries(num_free_entries)
  );

  // Ready bit
  cmn_MuxN #(
    .nbits  (1),
    .ninputs(noutputs)
  ) mux_inst (
    .in (ostream_rdy),
    .sel(select),
    .out(payload_rdy)
  );

  // Valid bit
  cmn_DemuxN #(
    .nbits   (1),
    .noutputs(noutputs)
  ) demux_inst (
    .in (payload_val),
    .sel(select),
    .out(ostream_val)
  );

  genvar i; 
  generate
    for (i = 0; i < noutputs; i = i + 1) begin : output_gen
      assign ostream_msg[i] = payload_msg;
    end
  endgenerate

  /* verilator lint_off UNUSED */
  logic unused = &{1'b0, num_free_entries, 1'b0};
  /* verilator lint_on UNUSED */
endmodule
`endif
//========================================================================
// Verilog Components: Demuxes
//========================================================================

`ifndef CMN_DEMUXES_V
`define CMN_DEMUXES_V

//------------------------------------------------------------------------
// N Input Demux
//------------------------------------------------------------------------

module cmn_DemuxN
#(
  parameter nbits = 1,   
  parameter noutputs = 2
)(
  input  logic                [nbits-1:0]   in,
  input  logic     [$clog2(noutputs)-1:0]   sel,
  output logic                [nbits-1:0]   out   [0:noutputs-1] 
); 

  genvar i;
  generate
    for (i = 0; i < noutputs; i = i + 1) begin : output_gen
      assign out[i] = (i == sel) ? in : {nbits{1'b0}};
    end
  endgenerate
endmodule

`endif /* CMN_DEMUXES_V */
`ifndef FIXED_POINT_FFT
`define FIXED_POINT_FFT


module fft_pease_FFT #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8 
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES],
  output logic                   send_val,
  input  logic                   send_rdy,

  input logic reset,
  input logic clk
);

  logic [2:0] IDLE = 3'd0, COMP = 3'd1, DONE = 3'd2;

  localparam int BstageBits = (N_SAMPLES > 2) ? $clog2($clog2(N_SAMPLES)) : 1;
  localparam int log = $clog2(N_SAMPLES) - 1;
  logic [BstageBits-1:0] max_bstage = log[BstageBits-1:0];

  logic [2:0] state;
  logic [2:0] next_state;

  assign recv_rdy = (state == IDLE || state == DONE);
  assign send_val = (state == DONE);

  logic [     BstageBits-1:0] bstage;
  logic [     BstageBits-1:0] next_bstage;

  logic [2 * BIT_WIDTH - 1:0] out_stride   [N_SAMPLES];
  logic [2 * BIT_WIDTH - 1:0] in_butterfly [N_SAMPLES];
  logic [2 * BIT_WIDTH - 1:0] out_butterfly[N_SAMPLES];

  logic [    BIT_WIDTH - 1:0] reversed_msg [N_SAMPLES];
  fft_helpers_BitReverse #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) bit_reverse (
    .in (recv_msg),
    .out(reversed_msg)
  );

  fft_pease_helpers_StridePermutation #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH * 2)
  ) stride_permutation (
    .recv(out_butterfly),
    .send(out_stride)
  );

  logic [BIT_WIDTH - 1:0] sine_wave_out[        N_SAMPLES];
  logic [BIT_WIDTH - 1:0] wr           [$clog2(N_SAMPLES)] [N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] wc           [$clog2(N_SAMPLES)] [N_SAMPLES/2];

  genvar i; 
  generate
    for (i = 0; i < $clog2(N_SAMPLES); i++) begin : for_2386 
      fft_pease_helpers_TwiddleGenerator #(
        .BIT_WIDTH (BIT_WIDTH),
        .DECIMAL_PT(DECIMAL_PT),
        .SIZE_FFT  (N_SAMPLES),
        .STAGE_FFT (i)
      ) twiddle_generator (
        .sine_wave_in(sine_wave_out),
        .twiddle_real(wr[i]),
        .twiddle_imaginary(wc[i])
      );
    end
  endgenerate

  fft_helpers_sine_wave_lookup_16_8_32 sine_wave ( 
    .sine_wave_out (sine_wave_out) 
  ); 


  logic [BIT_WIDTH - 1:0] ar[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] ac[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] br[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] bc[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] cr[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] cc[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] dr[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] dc[N_SAMPLES/2];

  generate
    for (i = 0; i < N_SAMPLES / 2; i++) begin : for_2419 
      assign ar[i] = in_butterfly[i*2][BIT_WIDTH-1:0];
      assign ac[i] = in_butterfly[i*2][2*BIT_WIDTH-1:BIT_WIDTH];
      assign br[i] = in_butterfly[i*2+1][BIT_WIDTH-1:0];
      assign bc[i] = in_butterfly[i*2+1][2*BIT_WIDTH-1:BIT_WIDTH];
      assign out_butterfly[i*2][BIT_WIDTH-1:0] = cr[i];
      assign out_butterfly[i*2][2*BIT_WIDTH-1:BIT_WIDTH] = cc[i];
      assign out_butterfly[i*2+1][BIT_WIDTH-1:0] = dr[i];
      assign out_butterfly[i*2+1][2*BIT_WIDTH-1:BIT_WIDTH] = dc[i];
    end
  endgenerate

  generate
    for (i = 0; i < N_SAMPLES; i++) begin : for_2432 
      assign send_msg[i] = in_butterfly[i][BIT_WIDTH-1:0];
    end
  endgenerate

  fixed_point_combinational_Butterfly #(
    .n(BIT_WIDTH),
    .d(DECIMAL_PT),
    .b(N_SAMPLES / 2)
  ) fft_stage (
    .wr(wr[bstage]),
    .wc(wc[bstage]),
    .*
  );

  always_comb begin
    next_state  = state;
    next_bstage = bstage;
    if (state == IDLE && recv_val) begin
      next_state = COMP;
    end else begin
      if (state == COMP) begin
        if (bstage == max_bstage) begin
          next_state  = DONE;
          next_bstage = 0;
        end else begin
          next_bstage = bstage + 1;
        end
      end else begin
        if (state == DONE && send_rdy) begin
          if (recv_val) begin
            next_state = COMP;
          end else begin
            next_state = IDLE;
          end
        end else begin
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (reset) begin
      state  <= IDLE;
      bstage <= 0;
    end else begin
      state  <= next_state;
      bstage <= next_bstage;
    end
  end

  generate
    for (i = 0; i < N_SAMPLES; i++) begin : for_2484 
      always_ff @(posedge clk) begin
        if (reset) begin
          in_butterfly[i] <= 0;
        end else begin
          if (state == IDLE || state == DONE && recv_val) begin
            in_butterfly[i][BIT_WIDTH-1:0] <= reversed_msg[i];
            in_butterfly[i][2*BIT_WIDTH-1:BIT_WIDTH] <= 0;
          end else begin
            if (state == COMP) begin
              in_butterfly[i] <= out_stride[i];
            end else begin
            end
          end
        end
      end
    end
  endgenerate

endmodule

`endif
`ifndef fft_helpers_SINE_WAVE
`define fft_helpers_SINE_WAVE
`default_nettype none

// Macro to generate a sine table for N evenly spaced values from 0 to 2pi.
// Returns values in a fixedpoint format with D fractional bits and W total bits.
`ifndef fft_helpers_BIT_REVERSE
`define fft_helpers_BIT_REVERSE
`default_nettype none

/// FFT Bit Reversal
/// @param BIT_WIDTH  : Data bit width
/// @param N_SAMPLES   : Number of points in the FFT
module fft_helpers_BitReverse #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8 
) (
  input  logic [BIT_WIDTH - 1:0] in [N_SAMPLES],
  output logic [BIT_WIDTH - 1:0] out[N_SAMPLES]
);
  // number of bits in an index
  localparam int n = $clog2(N_SAMPLES);

  genvar i; 
  genvar m; 
  generate
    if (N_SAMPLES == 8) begin
      assign out[0] = in[0];
      assign out[1] = in[4];
      assign out[2] = in[2];
      assign out[3] = in[6];
      assign out[4] = in[1];
      assign out[5] = in[5];
      assign out[6] = in[3];
      assign out[7] = in[7];
    end else begin
      for (m = 0; m < N_SAMPLES; m++) begin : for_2571 
        logic [n-1:0] m_rev;
        for (i = 0; i < n; i++) begin : for_2573 
          assign m_rev[n-i-1] = m[i];
        end
        assign out[m] = in[m_rev];
      end
    end
  endgenerate

endmodule

`endif
//================================================
// Iterative Butterfly Unit
// -----------------------------------------------
// This module performs the butterfly operation
// which is equivalent to the following matrix
// multiplication:
// | 1  w |   | a |   | c |
// | 1 -w | * | b | = | d |
// where w is the ith root of unity e^(-2*pi*i/n)
// and n/d is the fixed point specification`
// This module is used in the FFT module, and
// contains an area optimization parameter to
// save area by not including the complex
// multiplier in certain cases.
//================================================
`default_nettype none
`ifndef fixed_point_combinational_Butterfly
`define fixed_point_combinational_Butterfly

module fixed_point_combinational_Butterfly #(
  parameter int n = 32,
  parameter int d = 16,
  parameter int b = 4 
  // Number of inputs to rotate around
) (
  input logic [n-1:0] ar[b],
  input logic [n-1:0] ac[b],
  input logic [n-1:0] br[b],
  input logic [n-1:0] bc[b],
  input logic [n-1:0] wr[b],
  input logic [n-1:0] wc[b],

  output logic [n-1:0] cr[b],
  output logic [n-1:0] cc[b],
  output logic [n-1:0] dr[b],
  output logic [n-1:0] dc[b]
);

  /* performs the butterfly operation, equivalent to doing
    | 1  w |   | a |   | c |
    | 1 -w | * | b | = | d |
  */

  logic [n-1:0] m_cr[b];
  logic [n-1:0] m_cc[b];

  genvar i; 
  generate
    for (i = 0; i < b; i++) begin : for_2632 
      // complex multiplier instantiation as combinatorial
      fixed_point_combinational_ComplexMultiplierS #(
        .n(n),
        .d(d)
      ) mult (
        .ar(wr[i]),
        .ac(wc[i]),
        .br(br[i]),
        .bc(bc[i]),
        .cr(m_cr[i]),
        .cc(m_cc[i])
      );

      assign cc[i] = ac[i] + m_cc[i];
      assign cr[i] = ar[i] + m_cr[i];
      assign dc[i] = ac[i] - m_cc[i];
      assign dr[i] = ar[i] - m_cr[i];
    end
  endgenerate


endmodule
`endif
`default_nettype none
`ifndef FIXED_POINT_COMB_COMPLEX_MULTIPLIER
`define FIXED_POINT_COMB_COMPLEX_MULTIPLIER


/* Fully Combinational Complex Multipler.
 *
 * This modules contains three combinational multipliers, and 
 * performs a complex multiplication combinationally.
 *
 * 
 * 
 * Params:
 *  n: bit width 
 *  d: number of decimal bits
 * 
 * Inputs:
 *  ar, ac: real and complex parts of the first number
 *  br, bc: real and complex parts of the second number
 *
 * Outputs:
 *  cr, cc: real and complex parts of the result
 *
 * Tests: UNTESTED
 * Used In: N/A
 *
 * Author: Barry Lyu.
 * Date: Feb 14th 2024
 */
module fixed_point_combinational_ComplexMultiplierS #(
  parameter int n = 32,  // bit width
  parameter int d = 16   // number of decimal bits 
) (
  input  logic [n-1:0] ar,
  input  logic [n-1:0] ac,
  input  logic [n-1:0] br,
  input  logic [n-1:0] bc,
  output logic [n-1:0] cr,
  output logic [n-1:0] cc
);

  // cr = (ar * br) - (ac * bc)
  // cc = (ar * bc) + (br * ac) = (ar + ac)(br + bc) - (ac * bc) - (ar * br)
  logic [n-1:0] c_ar, c_ac, c_br, c_bc;
  logic [n-1:0] arXbr, acXbc, arcXbrc;

  assign c_ar = ar;
  assign c_ac = ac;
  assign c_br = br;
  assign c_bc = bc;

  fixed_point_combinational_Multiplier #(
    .n(n),
    .d(d),
    .sign(1)
  ) arXbrMult (
    .a(c_ar),
    .b(c_br),
    .c(arXbr)
  );

  fixed_point_combinational_Multiplier #(
    .n(n),
    .d(d),
    .sign(1)
  ) acXbcMult (
    .a(c_ac),
    .b(c_bc),
    .c(acXbc)
  );

  fixed_point_combinational_Multiplier #(
    .n(n),
    .d(d),
    .sign(1)
  ) arXbrcMult (
    .a(c_ar + c_ac),
    .b(c_br + c_bc),
    .c(arcXbrc)
  );

  assign cr = arXbr - acXbc;
  assign cc = arcXbrc - arXbr - acXbc;

endmodule

/* Parameterized Complex Multipler.
 *
 * ************************** IMPORTANT ***************************
 * Depending on num_mults, this module can be single or multi-cycle.
 * ************************** IMPORTANT ***************************
 *
 * This modules contains three combinational multipliers, and 
 * performs a complex multiplication combinationally.
 * 
 * Params:
 * - n: bit width 
 * - d: number of decimal bits
 * - num_mults: number of multipliers to use (1 or 3)
 *   - 1: single multiplier, multi-cycle (3 cycles with val/rdy)
 *   - 3: three multipliers, single-cycle (val/rdy connection optional)
 * 
 * Inputs:
 * - val/rdy interface: [recv_val, recv_rdy]
 *   - ar, ac: real and complex parts of the first number
 *   - br, bc: real and complex parts of the second number
 *
 * Outputs:
 * - val/rdy interface: send_val, send_rdy
 *   - cr, cc: real and complex parts of the result
 * 
 * Tests: FULLY_TESTED
 *  - tests/fixed_point/combinational/complex_multiplier_test.py [PASSED]
 *
 * Used In:
 *  - Combinational Multi-Butterfly Module: fixed_point/combinational/butterfly.v 
 *  
 * Author: Barry Lyu.
 * Date: Feb 14th 2024
 */
module fixed_point_combinational_ComplexMultiplier #(
  parameter int n = 32,  // bit width
  parameter int d = 16,  // number of decimal bits
  parameter int num_mults = 1  // number of multipliers 
) (
  input logic clk,
  input logic reset,
  input logic recv_val,
  output logic recv_rdy,
  output logic send_val,
  input logic send_rdy,
  input logic [n-1:0] ar,
  input logic [n-1:0] ac,
  input logic [n-1:0] br,
  input logic [n-1:0] bc,
  output logic [n-1:0] cr,
  output logic [n-1:0] cc
);
  // performs c = a * b on complex a and b

  // cr = (ar * br) - (ac * bc)
  // cc = (ar * bc) + (br * ac) = (ar + ac)(br + bc) - (ac * bc) - (ar * br)

  logic [n-1:0] c_ar, c_ac, c_br, c_bc;

  logic [n-1:0] arXbr, acXbc, arcXbrc;

  generate
    // 3 multiplier implementation, completes computations in a single cycle, no sequential logic required.
    if (num_mults == 3) begin
      assign c_ar = ar;
      assign c_ac = ac;
      assign c_br = br;
      assign c_bc = bc;

      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) arXbrMult (
        .a(c_ar),
        .b(c_br),
        .c(arXbr)
      );

      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) acXbcMult (
        .a(c_ac),
        .b(c_bc),
        .c(acXbc)
      );

      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) arXbrcMult (
        .a(c_ar + c_ac),
        .b(c_br + c_bc),
        .c(arcXbrc)
      );

      assign cr = arXbr - acXbc;
      assign cc = arcXbrc - arXbr - acXbc;
      assign recv_rdy = send_rdy;
      assign send_val = recv_val;

      logic unused = &({clk, reset});

      // 1 multiplier implementation, completes computations in three cycles.
    end else if (num_mults == 1) begin
      // State machine to control the 3-cycle computation
      logic [2:0] IDLE = 3'd0, MUL1 = 3'd1, MUL2 = 3'd2, MUL3 = 3'd3, DONE = 3'd4;
      logic [2:0] state;
      logic [2:0] next_state;

      // Intermediate results
      logic [n-1:0] mul_a, mul_b, mul_c;

      logic unused = &({IDLE, MUL1, MUL2, MUL3, DONE});

      always_ff @(posedge clk) begin
        if (reset) begin
          state <= IDLE;
          c_ar <= 0;
          c_ac <= 0;
          c_br <= 0;
          c_bc <= 0;
          arXbr <= 0;
          acXbc <= 0;
          arcXbrc <= 0;
        end else begin
          state <= next_state;
          if (state == IDLE && recv_val) begin
            // Store inputs in registers.
            c_ar <= ar;
            c_ac <= ac;
            c_br <= br;
            c_bc <= bc;
            arXbr <= 0;
            acXbc <= 0;
            arcXbrc <= 0;
          end else if (state == MUL1) begin
            arXbr <= mul_c;
          end else if (state == MUL2) begin
            acXbc <= mul_c;
          end else if (state == MUL3) begin
            arcXbrc <= mul_c;
          end else begin
          end
        end
      end

      always_comb begin
        // Combinational logic for the next state.
        next_state = state;
        recv_rdy = 0;
        send_val = 0;
        mul_a = 0;
        mul_b = 0;

        case (state)
          IDLE: begin
            recv_rdy = 1;
            if (recv_val) next_state = MUL1;
            else next_state = IDLE;
          end
          MUL1: begin
            next_state = MUL2;
            mul_a = c_ar;
            mul_b = c_br;
          end
          MUL2: begin
            next_state = MUL3;
            mul_a = c_ac;
            mul_b = c_bc;
          end
          MUL3: begin
            next_state = DONE;
            mul_a = c_ar + c_ac;
            mul_b = c_br + c_bc;
          end
          DONE: begin
            send_val = 1;
            if (send_rdy) next_state = IDLE;
            else next_state = state;
          end
          default: begin
          end
        endcase
      end

      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) arXbrMult (
        .a(mul_a),
        .b(mul_b),
        .c(mul_c)
      );

      assign cr = arXbr - acXbc;
      assign cc = arcXbrc - arXbr - acXbc;
    end
  endgenerate
endmodule

`endif
`default_nettype none
`ifndef FIXED_POINT_COMB_MULTIPLIER
`define FIXED_POINT_COMB_MULTIPLIER

module fixed_point_combinational_Multiplier #(
  parameter int n = 32,  // bit width
  parameter int d = 16,  // number of decimal bits
  parameter bit sign = 1  // 1 if signed 
) (
  input  logic [n-1:0] a,
  input  logic [n-1:0] b,
  output logic [n-1:0] c
);

  logic [d+n-1:0] prod;
  logic [d+n-1:0] a_ext, b_ext;

  generate
    if (sign) begin
      assign a_ext = {{d{a[n-1]}}, a};
      assign b_ext = {{d{b[n-1]}}, b};
      assign prod  = (a_ext * b_ext);
    end else begin
      assign prod = (a * b);
    end
  endgenerate

  assign c = prod[n+d-1:d];


  // The upper n bits of prod are discarded.
  generate
    if (d > 0) begin
      /* verilator lint_off UNUSED */
      logic unused;
      /* verilator lint_on UNUSED */
      assign unused = &{1'b0, prod[d-1:0], 1'b0};
    end
  endgenerate

endmodule

`endif
`ifndef fft_pease_helpers_STRIDE_PERMUTATION
`define fft_pease_helpers_STRIDE_PERMUTATION

/// Takes a bus of width `N_SAMPLES` and performs a stride permutation on it.
/// Described on page 33 of https://link.springer.com/chapter/10.1007/978-1-4757-2767-8_2
/// @param N_SAMPLES The number of samples in the bus. Must be divisible by two.
/// @param WIDTH The width of each sample in the bus.
module fft_pease_helpers_StridePermutation #(
  parameter int N_SAMPLES = 8,
  parameter int BIT_WIDTH = 32 
) (
  input  logic [BIT_WIDTH-1:0] recv[N_SAMPLES],
  output logic [BIT_WIDTH-1:0] send[N_SAMPLES]
);

  genvar i; 
  generate
    for (i = 0; i < N_SAMPLES / 2; i++) begin : for_3008 
      assign send[i] = recv[i*2];
      assign send[i+N_SAMPLES/2] = recv[i*2+1];
    end
  endgenerate

endmodule

`endif
`ifndef fft_pease_helpers_TWIDDLE_GENERATOR
`define fft_pease_helpers_TWIDDLE_GENERATOR

/// Twiddle Generator module for a stage in a pease FFT
module fft_pease_helpers_TwiddleGenerator #(
  parameter int BIT_WIDTH  = 4,
  parameter int DECIMAL_PT = 2,
  parameter int SIZE_FFT   = 8,
  parameter int STAGE_FFT  = 0 
) (
  input logic [BIT_WIDTH - 1:0] sine_wave_in[SIZE_FFT],  //sine_wave_in = sin(2*pi m / N)

  output logic [BIT_WIDTH - 1:0] twiddle_real     [SIZE_FFT/2],
  output logic [BIT_WIDTH - 1:0] twiddle_imaginary[SIZE_FFT/2]
);
  genvar j; 
  genvar m; 
  genvar i; 
  generate
    if (STAGE_FFT == 0) begin
      for (i = 0; i < SIZE_FFT / 2; i = i + 1) begin : for_3037 
        assign twiddle_real[i] = {{BIT_WIDTH - DECIMAL_PT - 1{1'b0}}, 1'b1, {DECIMAL_PT{1'b0}}};
        assign twiddle_imaginary[i] = 0;
      end
      logic unused = &sine_wave_in;
    end else begin

      for (m = 0; m < 2 ** STAGE_FFT; m = m + 1) begin : for_3044 
        for (j = 0; j < 2 ** ($clog2(SIZE_FFT) - STAGE_FFT - 1); j = j + 1) begin : for_3045 
          localparam int stageLeft = $clog2(SIZE_FFT) - STAGE_FFT - 1;
          localparam int idx = m * (2 ** stageLeft);
          localparam int si = idx + j;
          assign twiddle_real[si] = sine_wave_in[idx+SIZE_FFT/4];
          assign twiddle_imaginary[si] = sine_wave_in[idx+SIZE_FFT/2];
        end
      end
    end
  endgenerate

endmodule

`endif
`default_nettype none
`ifndef serdes_DESERIALIZER
`define serdes_DESERIALIZER 

module serdes_Deserializer #(
  parameter int N_SAMPLES = 8,
  parameter int BIT_WIDTH = 32 
) (

  input logic recv_val,
  output logic recv_rdy,
  input logic [BIT_WIDTH - 1:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES],

  input logic clk,
  input logic reset
);

  genvar i; 
  generate
    if (N_SAMPLES == 1) begin
      assign recv_rdy = send_rdy;
      assign send_val = recv_val;
      assign send_msg[0] = recv_msg;

      logic unused = {1'b0, clk, reset, 1'b0};
    end else begin
      logic [N_SAMPLES - 1:0] en_sel;

      //body of code
      DeserializerControl #(
        .N_SAMPLES(N_SAMPLES)
      ) c (
        .recv_val(recv_val),
        .send_rdy(send_rdy),

        .send_val(send_val),
        .recv_rdy(recv_rdy),

        .reset(reset),
        .clk  (clk),

        .en_sel(en_sel)
      );

      for (i = 0; i < N_SAMPLES; i++) begin : l_regs
        cmn_EnResetReg #(BIT_WIDTH) register (
          .clk(clk),
          .reset(reset),
          .en(recv_rdy & en_sel[i]),
          .d(recv_msg),
          .q(send_msg[i])
        );
      end
    end
  endgenerate

endmodule

module DeserializerControl #(
  parameter int N_SAMPLES = 8 
) (
  input logic recv_val,
  input logic send_rdy,

  output logic send_val,
  output logic recv_rdy,

  output logic [N_SAMPLES - 1:0] en_sel,

  input logic reset,
  input logic clk
);
  logic INIT = 1'b0, DONE = 1'b1;

  localparam int C_WIDTH = $clog2(N_SAMPLES) - 1;
  // Necessary because counter_next can go up to (including) N_SAMPLES
  // so we need an extra bit to avoid overflow.
  localparam int C_NXT_WIDTH = $clog2(N_SAMPLES + 1) - 1;
  logic [C_WIDTH:0] count;  //counter
  logic [C_NXT_WIDTH:0] count_next;

  logic next_state;
  logic state;

  Decoder #($clog2(
      N_SAMPLES
  )) decoder (
    .in (count),
    .out(en_sel)
  );

  always_comb begin
    case (state)
      INIT: begin
        if (count_next == N_SAMPLES[C_NXT_WIDTH:0]) begin
          next_state = DONE;
        end else begin
          next_state = INIT;
        end
      end
      DONE: begin
        if (send_rdy == 1) begin
          next_state = INIT;
        end else begin
          next_state = DONE;
        end
      end
      default: next_state = INIT;
    endcase
  end

  always_comb begin
    case (state)
      INIT: begin
        if (recv_val == 1) begin
          count_next = {{(C_NXT_WIDTH - C_WIDTH) {1'b0}}, count} + 1;
        end else begin
          count_next = {{(C_NXT_WIDTH - C_WIDTH) {1'b0}}, count};
        end

        recv_rdy = 1'b1;
        send_val = 1'b0;
      end

      DONE: begin
        count_next = 0;
        recv_rdy   = 1'b0;
        send_val   = 1'b1;
      end

      default: begin
        count_next = 0;
        recv_rdy   = 1'b1;
        send_val   = 1'b0;
      end

    endcase

  end

  always_ff @(posedge clk) begin
    if (reset) begin
      count <= 0;
      state <= INIT;
    end else begin
      count <= count_next[$clog2(N_SAMPLES)-1:0];
      state <= next_state;
    end
  end
endmodule

module Decoder #(
  parameter int BIT_WIDTH = 3 
) (
  input logic [BIT_WIDTH - 1:0] in,
  output logic [(1 << BIT_WIDTH) - 1:0] out
);
  assign out = {{(1 << BIT_WIDTH) - 1{1'b0}}, 1'b1} << in;
endmodule
`endif
`default_nettype none
`ifndef serdes_SERIALIZER
`define serdes_SERIALIZER

module serdes_Serializer #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8 
) (
  input logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],
  input logic recv_val,
  output logic recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic send_val,
  input logic send_rdy,

  input logic reset,
  input logic clk
);
  genvar i; 
  generate
    if (N_SAMPLES == 1) begin
      assign recv_rdy = send_rdy;
      assign send_val = recv_val;
      assign send_msg = recv_msg[0];

      logic unused = {1'b0, clk, reset, 1'b0};
    end else begin
      logic [$clog2(N_SAMPLES) - 1:0] mux_sel;
      logic reg_en;
      logic [BIT_WIDTH - 1:0] reg_out[N_SAMPLES - 1:0];

      for (i = 0; i < N_SAMPLES; i++) begin : l_regs
        cmn_EnResetReg #(BIT_WIDTH) register (
          .clk(clk),
          .reset(reset),
          .en(reg_en),
          .d(recv_msg[i]),
          .q(reg_out[i])
        );
      end

      assign send_msg = reg_out[mux_sel];

      SerializerControl #(
        .N_SAMPLES(N_SAMPLES)
      ) ctrl (
        .clk(clk),
        .reset(reset),
        .recv_val(recv_val),
        .recv_rdy(recv_rdy),
        .send_val(send_val),
        .send_rdy(send_rdy),
        .mux_sel(mux_sel),
        .reg_en(reg_en)
      );
    end
  endgenerate
endmodule


module SerializerControl #(
  parameter int N_SAMPLES = 8 
) (
  input  logic recv_val,
  output logic recv_rdy,

  output logic send_val,
  input  logic send_rdy,

  output logic [$clog2(N_SAMPLES) - 1:0] mux_sel,
  output logic reg_en,

  input logic clk,
  input logic reset
);

  logic INIT = 1'b0, OUTPUT_START = 1'b1;

  logic next_state;
  logic state;

  // Number of bits to represent N_SAMPLES-1
  localparam int NS_EXC_W = $clog2(N_SAMPLES);
  // Number of bits to represent N_SAMPLES
  localparam int NS_W = $clog2(N_SAMPLES + 1);
  logic [NS_W-1:0] mux_sel_next;

  always_comb begin
    case (state)
      INIT: begin
        if (reset == 1) next_state = INIT;
        else if (recv_val == 1) next_state = OUTPUT_START;
        else next_state = INIT;
      end
      OUTPUT_START: begin
        if (mux_sel_next != N_SAMPLES[NS_W-1:0]) next_state = OUTPUT_START;
        else next_state = INIT;
      end
      default: next_state = INIT;
    endcase
  end

  always_comb begin
    case (state)
      INIT: begin
        reg_en = 1;
        send_val = 0;
        recv_rdy = 1;
        mux_sel_next = 0;
      end
      OUTPUT_START: begin
        reg_en   = 0;
        send_val = 1;
        recv_rdy = 0;
        if (send_rdy == 1) mux_sel_next = {{(NS_W - NS_EXC_W) {1'b0}}, mux_sel} + 1;
        else mux_sel_next = {{(NS_W - NS_EXC_W) {1'b0}}, mux_sel};
      end
      default: begin
        reg_en = 1;
        send_val = 0;
        recv_rdy = 1;
        mux_sel_next = 0;
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (reset) begin
      state   <= INIT;
      mux_sel <= 0;
    end else begin
      mux_sel <= mux_sel_next[NS_EXC_W-1:0];
      state   <= next_state;
    end
  end
endmodule
`endif
`ifndef arbiter_router_ARBITER
`define arbiter_router_ARBITER
/*
  ==========================================================================
  Arbitrator module
  ==========================================================================
  This module is used to pick which component gets to output to the val/rdy
  SPI wrapper if multiple components can send a valid message.
  The arbitrator puts an address header on the outgoing packet so that
  downstream components can tell which component sent the response
  The nbits parameter is the length of the message.
  
  The num_inputs parameter is the number of input components that the
  Arbitrator is selecting from.
  NOTE: MUST be >= 2

  Original Author  : Dilan Lakhani
  Date             : Dec 19, 2021
*/

module arbiter_router_Arbiter #(
  parameter int nbits = 32,
  parameter int ninputs = 3 
) (
  input logic clk,
  input logic reset,

  // Receive Interface - need recv signals for each component connected to arbitrator
  input  logic             istream_val[ninputs],
  output logic             istream_rdy[ninputs],
  input  logic [nbits-1:0] istream_msg[ninputs],

  // Send Interface
  output logic                        ostream_val,
  input  logic                        ostream_rdy,
  output logic [addr_nbits+nbits-1:0] ostream_msg
);
  localparam int addr_nbits = $clog2(ninputs); 
  logic [addr_nbits-1:0] grants_index;  // which input is granted access to send to SPI
  logic [addr_nbits-1:0] old_grants_index;
  logic [addr_nbits-1:0] encoder_out;
  logic [     nbits-1:0] ostream_msg_data;
  logic [addr_nbits-1:0] ostream_msg_addr;

  assign ostream_msg_data = istream_msg[grants_index];
  assign ostream_msg_addr = grants_index;
  assign ostream_val = istream_val[grants_index] & istream_rdy[grants_index];
  assign ostream_msg = {
    ostream_msg_addr, ostream_msg_data
  };  // append component address to the beginning of the message  


  always_comb begin
    // change grants_index if the last cycle's grant index is 0
    // (that component has finished sending its message)
    if (!istream_val[old_grants_index]) begin
      grants_index = encoder_out;
    end else begin
      grants_index = old_grants_index;
    end
  end

  genvar i; 
  generate
    for (i = 0; i < ninputs; i++) begin : input_assign
      // Only tell one input that the arbitrator is ready for it
      assign istream_rdy[i] = (grants_index == i[addr_nbits-1:0]) ? ostream_rdy : 1'b0;
    end
  endgenerate

  generate
    // hooks up a chain of muxes to create a
    // priority encoder that gives highest priority to the LSB and lowest to MSB
    // Disable unoptflat because there isn't actually circular logic as different
    // indices are accessed each time
    /* verilator lint_off UNOPTFLAT */
    logic [addr_nbits-1:0] encoder_outs[ninputs+1];
    /* verilator lint_on UNOPTFLAT */
    assign encoder_outs[ninputs] = 0;
    for (i = 0; i < ninputs; i++) begin : for_3440 
      // if this input is valid, then it is the highest priority. Otherwise, use the result of the next index
      assign encoder_outs[i] = istream_val[i] ? i : encoder_outs[i+1];
    end
    assign encoder_out = encoder_outs[0];
  endgenerate

  /*
    One issue arises with having multiple Disassemblers.
    Since the SPI width is normally less than the size of a response,
    a PacketDisassembler component needs multiple cycles to fully send a message to the arbitrator.
    Thus, we do not want to change which Disassembler is allowed to send to the Arbitrator
    in the middle of a message. Fix this by holding a trailing value of the grants_index.
    We need to be able to check the req_val of the old grants_index to make sure that it
    is not 1, then we can allow a different Disassembler to send a message.
  */

  always_ff @(posedge clk) begin
    if (reset) begin
      old_grants_index <= 0;
    end else begin
      old_grants_index <= grants_index;
    end
  end

endmodule
`endif
`ifndef PROJECT_CROSSBAR_V
`define PROJECT_CROSSBAR_V 

//Crossbar in Verilog

module crossbars_Blocking #(
  parameter int BIT_WIDTH = 32,
  parameter int N_INPUTS = 2,
  parameter int N_OUTPUTS = 2 
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_INPUTS],
  input  logic                   recv_val[N_INPUTS],
  output logic                   recv_rdy[N_INPUTS],

  output logic [BIT_WIDTH - 1:0] send_msg[N_OUTPUTS],
  output logic                   send_val[N_OUTPUTS],
  input  logic                   send_rdy[N_OUTPUTS],

  input logic reset,
  input logic clk,

  input  logic [CONTROL_BIT_WIDTH - 1:0] control,
  input  logic                           control_val,
  output logic                           control_rdy
);
  localparam int CONTROL_BIT_WIDTH = $clog2(N_INPUTS * N_OUTPUTS); 

  logic [CONTROL_BIT_WIDTH - 1:0] stored_control;
  logic [$clog2(N_INPUTS)  - 1:0] input_sel;
  logic [$clog2(N_OUTPUTS) - 1:0] output_sel;

  always_ff @(posedge clk) begin
    if (reset) begin
      stored_control <= 0;
    end else if (control_val) begin
      stored_control <= control;
    end else begin
      stored_control <= stored_control;
    end
  end

  assign control_rdy = 1;



  assign input_sel = stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)];

  assign output_sel = stored_control[CONTROL_BIT_WIDTH-$clog2(
      N_INPUTS
  )-1 : CONTROL_BIT_WIDTH-$clog2(
      N_INPUTS
  )-$clog2(
      N_OUTPUTS
  )];

  always_comb begin
    for (int i = 0; i < N_OUTPUTS; i = i + 1) begin : for_3523 
      /* verilator lint_off WIDTH */
      if ((i != output_sel)) begin
        /* verilator lint_on WIDTH */
        send_msg[i] = 0;
        send_val[i] = 0;
      end else begin
        send_msg[i] = recv_msg[input_sel];
        send_val[i] = recv_val[input_sel];
      end
    end
    for (int i = 0; i < N_INPUTS; i = i + 1) begin : for_3534 
      /* verilator lint_off WIDTH */
      if ((i != input_sel)) begin
        /* verilator lint_on WIDTH */
        recv_rdy[i] = 0;
      end else begin
        recv_rdy[i] = send_rdy[output_sel];
      end
    end
  end

endmodule

`endif
//================================================
// classifier.v
//================================================
`default_nettype none
`ifndef CLASSIFIER_V
`define CLASSIFIER_V

module classifier_Classifier #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  // bit width used for frequency calculations
  // this should be large enough to handle the sampling frequency
  parameter int FREQ_BIT_WIDTH = 16,
  parameter int N_SAMPLES = 8 
) (
  input logic clk,
  input logic reset,

  output logic                   recv_rdy,
  input  logic                   recv_val,
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],

  output logic                        cutoff_freq_rdy,
  input  logic                        cutoff_freq_val,
  input  logic [FREQ_BIT_WIDTH - 1:0] cutoff_freq_msg,

  output logic                   cutoff_mag_rdy,
  input  logic                   cutoff_mag_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_mag_msg,

  output logic                        sampling_freq_rdy,
  input  logic                        sampling_freq_val,
  input  logic [FREQ_BIT_WIDTH - 1:0] sampling_freq_msg,

  input  logic send_rdy,
  output logic send_val,
  output logic send_msg
);

  logic [FREQ_BIT_WIDTH-1:0] in_cutoff_freq;
  logic [BIT_WIDTH-1:0] in_cutoff_mag;
  logic [FREQ_BIT_WIDTH-1:0] in_sampling_freq;

  cmn_EnResetReg #(
    .p_nbits      (FREQ_BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_freq_in (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_freq_msg),
    .q    (in_cutoff_freq),
    .en   (cutoff_freq_val)
  );
  assign cutoff_freq_rdy = 1;

  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_mag_in (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_mag_msg),
    .q    (in_cutoff_mag),
    .en   (cutoff_mag_val)
  );
  assign cutoff_mag_rdy = 1;

  cmn_EnResetReg #(
    .p_nbits      (FREQ_BIT_WIDTH),
    .p_reset_value(0)
  ) sampling_freq_in (
    .clk  (clk),
    .reset(reset),
    .d    (sampling_freq_msg),
    .q    (in_sampling_freq),
    .en   (sampling_freq_val)
  );
  assign sampling_freq_rdy = 1;

  // Calculate the magnitude combinational
  logic [BIT_WIDTH-1:0] out_mag[N_SAMPLES];

  magnitude_Magnitude #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) mag_calc (
    .recv_msg(recv_msg),
    .send_msg(out_mag)
  );

  // Filter based on cutoff
  logic [FREQ_BIT_WIDTH-1:0] frequency_array[N_SAMPLES];

  classifier_helpers_FrequencyBins #(
    .BIT_WIDTH(FREQ_BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) freq_gen (
    .sampling_freq(in_sampling_freq),
    .frequency_out(frequency_array)
  );

  logic out_filter[N_SAMPLES];

  highpass_Highpass #(
    .BIT_WIDTH(FREQ_BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) highpass_fil (
    .cutoff_freq(in_cutoff_freq),
    .freq_in(frequency_array),
    .filtered_valid(out_filter)
  );

  // Do comparison mag > cutoff_mag
  logic out_comparison;

  comparison_Comparison #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) comparison (
    .cutoff_mag(in_cutoff_mag),
    .filtered_valid(out_filter),
    .mag_in(out_mag),
    .compare_out(out_comparison)
  );

  assign send_msg = out_comparison;
  assign send_val = recv_val;
  assign recv_rdy = send_rdy;
endmodule

`endif
//================================================
// magnitude.v
//================================================
`default_nettype none
`ifndef MAGNITUDE_V
`define MAGNITUDE_V

module magnitude_Magnitude #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8 
) (
  input logic signed [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],
  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES]
);
  genvar i; 
  generate
    for (i = 0; i < N_SAMPLES; i = i + 1) begin : for_3695 
      assign send_msg[i] = (recv_msg[i] < 0) ? -recv_msg[i] : recv_msg[i];
    end
  endgenerate

endmodule

`endif
//================================================
// highpass.v
//================================================
`default_nettype none
`ifndef HIGHPASS_V
`define HIGHPASS_V

module highpass_Highpass #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8 
) (
  input  logic [BIT_WIDTH - 1:0] cutoff_freq,
  input  logic [BIT_WIDTH - 1:0] freq_in       [N_SAMPLES],
  output logic                   filtered_valid[N_SAMPLES]
);

  genvar i; 
  generate
    for (i = 0; i < N_SAMPLES; i = i + 1) begin : for_3721 
      assign filtered_valid[i] = freq_in[i] > cutoff_freq;
    end
  endgenerate


endmodule

`endif
//================================================
// frequency_bins.v
//================================================
`default_nettype none
`ifndef FREQUENCY_BINS_V
`define FREQUENCY_BINS_V

// Calculates the frequency bins of an FFT
// Requires that N_SAMPLES is a power of 2
module classifier_helpers_FrequencyBins #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 16 
) (
  input  logic [BIT_WIDTH - 1:0] sampling_freq,
  output logic [BIT_WIDTH - 1:0] frequency_out[N_SAMPLES]
);

  localparam int LOG2_N_SAMPLES = $clog2(N_SAMPLES);

  initial begin
    if ($pow(2, LOG2_N_SAMPLES) != N_SAMPLES) begin
    end
  end

  // We make the sampling frequency a bit wider to avoid overflow
  wire [LOG2_N_SAMPLES + BIT_WIDTH - 1:0] wide_sampling_freq = {
    (LOG2_N_SAMPLES)'(0), sampling_freq
  };

  genvar i; 
  generate
    for (i = 0; i < N_SAMPLES; i++) begin : gen_freq
      wire [LOG2_N_SAMPLES + BIT_WIDTH - 1:0] wide_freq_out = (i * wide_sampling_freq) >> (LOG2_N_SAMPLES + 1);
      assign frequency_out[i] = wide_freq_out[BIT_WIDTH-1:0];

      wire unused = &{1'b0, wide_freq_out[LOG2_N_SAMPLES+BIT_WIDTH-1:BIT_WIDTH], 1'b0};
    end
  endgenerate

endmodule

`endif
//================================================
// comparison.v
//================================================
`default_nettype none
`ifndef COMPARISON_V
`define COMPARISON_V

module comparison_Comparison #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8 
) (
  input  logic [BIT_WIDTH - 1:0] cutoff_mag,
  input  logic                   filtered_valid[N_SAMPLES],
  input  logic [BIT_WIDTH - 1:0] mag_in        [N_SAMPLES],
  output logic                   compare_out
);
  logic [N_SAMPLES-1:0] compare_outs;

  genvar i; 
  generate
    for (i = 0; i < N_SAMPLES; i = i + 1) begin : for_3793 
      assign compare_outs[i] = filtered_valid[i] & (mag_in[i] > cutoff_mag);
    end
  endgenerate

  assign compare_out = compare_outs != 0;
endmodule

`endif
//========================================================================
// Register Array Implementation
//========================================================================

`ifndef REG_ARRAY_V
`define REG_ARRAY_V
`define CMN_QUEUE_NORMAL 4'b0000


module wishbone_Wishbone #(
  // parameter p_msg_nbits = 1,
  parameter int p_num_msgs = 2,
  parameter int p_num_istream = 2,
  parameter int p_num_ostream = 2 

  // Local constants not meant to be set from outside the module
) (
  // Wishbone Slave ports (WB MI A)
  input logic clk,
  input logic reset,
  input logic wbs_stb_i,
  input logic wbs_cyc_i,
  input logic wbs_we_i,
  input logic [3:0] wbs_sel_i,
  input logic [31:0] wbs_dat_i,
  input logic [31:0] wbs_adr_i,
  output logic wbs_ack_o,
  output logic [31:0] wbs_dat_o,

  // Ports to connect to modules
  input  logic istream_rdy[p_num_istream],
  output logic istream_val[p_num_istream],

  output logic ostream_rdy[p_num_ostream],
  input  logic ostream_val[p_num_ostream],

  input  logic [31:0] ostream_data[p_num_ostream],
  output logic [31:0] istream_data[p_num_istream]
);
  localparam int ostream_addr_nbits = $clog2(p_num_ostream); 
  localparam int istream_addr_nbits = $clog2(p_num_istream); 
  localparam int c_addr_nbits = $clog2(p_num_msgs); 
  /////////////////
  // address decoder
  //////////////////
  localparam int ISTREAM_BASE = 32'h3000_0000;  // istream base address
  localparam int OSTREAM_BASE = ISTREAM_BASE + p_num_istream * 8;  // ostream base address

  logic transaction_val;
  assign transaction_val = wbs_stb_i && wbs_cyc_i;

  logic [31:0] adr_sub;
  cmn_Subtractor #(32) ostream_addr_sub (
    .in0(wbs_adr_i),
    .in1(OSTREAM_BASE),
    .out(adr_sub)
  );

  logic is_check_istream;
  assign is_check_istream = (wbs_adr_i >= ISTREAM_BASE)
    && (wbs_adr_i < OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'b0)
    && transaction_val && !wbs_we_i;
  logic [istream_addr_nbits-1:0] istream_check_ind;

  logic is_write_istream;
  assign is_write_istream = (wbs_adr_i >= ISTREAM_BASE)
    && (wbs_adr_i < OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'd4)
    && transaction_val && wbs_we_i;
  logic [istream_addr_nbits-1:0] istream_write_ind;

  logic is_check_ostream;
  assign is_check_ostream = (wbs_adr_i >= OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'b0)
    && transaction_val
    && !wbs_we_i;
  logic [ostream_addr_nbits-1:0] ostream_check_ind;

  logic is_read_ostream;
  assign is_read_ostream = (wbs_adr_i >= OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'd4)
    && transaction_val
    && !wbs_we_i;
  logic [ostream_addr_nbits-1:0] ostream_read_ind;

  assign istream_check_ind = wbs_adr_i[istream_addr_nbits-1+3:3];
  assign istream_write_ind = wbs_adr_i[istream_addr_nbits-1+3:3];
  assign ostream_check_ind = adr_sub[ostream_addr_nbits-1+3:3];
  assign ostream_read_ind  = adr_sub[ostream_addr_nbits-1+3:3];

  /////////////////
  // istream queue
  //////////////////

  logic istream_enq_val[p_num_istream];
  logic istream_enq_rdy[p_num_istream];
  logic [31:0] istream_enq_msg[p_num_istream];

  genvar i; 
  generate
    for (i = 0; i < p_num_istream; i++) begin : g_istream_enq_gen
      assign istream_enq_val[i] = (is_write_istream && (istream_write_ind == i)) ? 1'b1 : 1'b0;
      assign istream_enq_msg[i] = (is_write_istream && (istream_write_ind == i)) ? wbs_dat_i : 32'b0;
    end
  endgenerate


  genvar n; 
  generate
    for (n = 0; n < p_num_istream; n = n + 1) begin : g_istream_queue_gen
      cmn_Queue #(`CMN_QUEUE_NORMAL, 32, p_num_msgs) istream_queue (
        .clk(clk),
        .reset(reset),
        .enq_val(istream_enq_val[n]),
        .enq_rdy(istream_enq_rdy[n]),
        .enq_msg(istream_enq_msg[n]),
        .deq_val(istream_val[n]),
        .deq_rdy(istream_rdy[n]),
        .deq_msg(istream_data[n]),
        /* verilator lint_off PINCONNECTEMPTY */
        .num_free_entries()
        /* verilator lint_on PINCONNECTEMPTY */
      );
    end
  endgenerate

  //////////////////
  // ostream queue
  //////////////////

  logic [p_num_ostream-1:0] ostream_deq_val;
  logic [p_num_ostream-1:0] ostream_deq_rdy;
  logic [31:0] ostream_deq_msg[p_num_ostream];

  generate
    for (i = 0; i < p_num_ostream; i++) begin : g_ostream_enq_gen
      assign ostream_deq_rdy[i] = (is_read_ostream && (ostream_read_ind == i)) ? 1'b1 : 1'b0;
    end
  endgenerate

  genvar m; 
  generate
    for (m = 0; m < p_num_ostream; m = m + 1) begin : g_ostream_queue_gen
      cmn_Queue #(`CMN_QUEUE_NORMAL, 32, p_num_msgs) ostream_queue (
        .clk(clk),
        .reset(reset),
        .enq_val(ostream_val[m]),
        .enq_rdy(ostream_rdy[m]),
        .enq_msg(ostream_data[m]),
        .deq_val(ostream_deq_val[m]),
        .deq_rdy(ostream_deq_rdy[m]),
        .deq_msg(ostream_deq_msg[m]),
        /* verilator lint_off PINCONNECTEMPTY */
        .num_free_entries()
        /* verilator lint_on PINCONNECTEMPTY */
      );
    end
  endgenerate


  //////////////
  // set outputs
  /////////////
  always_comb begin
    if (is_check_istream) wbs_dat_o = {31'b0, istream_enq_rdy[istream_check_ind]};
    else if (is_check_ostream) wbs_dat_o = {31'b0, ostream_deq_val[ostream_check_ind]};
    else if (is_read_ostream) wbs_dat_o = ostream_deq_msg[ostream_read_ind];
    else wbs_dat_o = 32'b0;
  end


  assign wbs_ack_o = 1'b1;


  // Unused Net
  logic unused = &{1'b0, wbs_sel_i, adr_sub, 1'b0};
endmodule

`endif  /* REG_ARRAY_V */
//========================================================================
// Verilog Components: Arithmetic Components
//========================================================================

`ifndef CMN_ARITHMETIC_V
`define CMN_ARITHMETIC_V

//------------------------------------------------------------------------
// Adders
//------------------------------------------------------------------------

module cmn_Adder #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  input  logic [p_nbits-1:0] in1,
  input  logic               cin,
  output logic [p_nbits-1:0] out,
  output logic               cout
);

  // We need to convert cin into a 32-bit value to
  // avoid verilator warnings

  assign {cout, out} = in0 + in1 + {{(p_nbits - 1) {1'b0}}, cin};

endmodule

module cmn_SimpleAdder #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  input  logic [p_nbits-1:0] in1,
  output logic [p_nbits-1:0] out
);

  assign out = in0 + in1;

endmodule

//------------------------------------------------------------------------
// Subtractor
//------------------------------------------------------------------------

module cmn_Subtractor #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  input  logic [p_nbits-1:0] in1,
  output logic [p_nbits-1:0] out
);

  assign out = in0 - in1;

endmodule

//------------------------------------------------------------------------
// Incrementer
//------------------------------------------------------------------------

module cmn_Incrementer #(
  parameter p_nbits     = 1,
  parameter p_inc_value = 1 
) (
  input  logic [p_nbits-1:0] in,
  output logic [p_nbits-1:0] out
);

  assign out = in + p_inc_value;

endmodule

//------------------------------------------------------------------------
// ZeroExtender
//------------------------------------------------------------------------

module cmn_ZeroExtender #(
  parameter p_in_nbits  = 1,
  parameter p_out_nbits = 8 
) (
  input  logic [ p_in_nbits-1:0] in,
  output logic [p_out_nbits-1:0] out
);

  assign out = {{(p_out_nbits - p_in_nbits) {1'b0}}, in};

endmodule

//------------------------------------------------------------------------
// SignExtender
//------------------------------------------------------------------------

module cmn_SignExtender #(
  parameter p_in_nbits  = 1,
  parameter p_out_nbits = 8 
) (
  input  logic [ p_in_nbits-1:0] in,
  output logic [p_out_nbits-1:0] out
);

  assign out = {{(p_out_nbits - p_in_nbits) {in[p_in_nbits-1]}}, in};

endmodule

//------------------------------------------------------------------------
// ZeroComparator
//------------------------------------------------------------------------

module cmn_ZeroComparator #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in,
  output logic               out
);

  assign out = (in == {p_nbits{1'b0}});

endmodule

//------------------------------------------------------------------------
// EqComparator
//------------------------------------------------------------------------

module cmn_EqComparator #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  input  logic [p_nbits-1:0] in1,
  output logic               out
);

  assign out = (in0 == in1);

endmodule

//------------------------------------------------------------------------
// LtComparator
//------------------------------------------------------------------------

module cmn_LtComparator #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  input  logic [p_nbits-1:0] in1,
  output logic               out
);

  assign out = (in0 < in1);

endmodule

//------------------------------------------------------------------------
// GtComparator
//------------------------------------------------------------------------

module cmn_GtComparator #(
  parameter p_nbits = 1 
) (
  input  logic [p_nbits-1:0] in0,
  input  logic [p_nbits-1:0] in1,
  output logic               out
);

  assign out = (in0 > in1);

endmodule

//------------------------------------------------------------------------
// LeftLogicalShifter
//------------------------------------------------------------------------

module cmn_LeftLogicalShifter #(
  parameter p_nbits       = 1,
  parameter p_shamt_nbits = 1 
) (
  input  logic [      p_nbits-1:0] in,
  input  logic [p_shamt_nbits-1:0] shamt,
  output logic [      p_nbits-1:0] out
);

  assign out = (in << shamt);

endmodule

//------------------------------------------------------------------------
// RightLogicalShifter
//------------------------------------------------------------------------

module cmn_RightLogicalShifter #(
  parameter p_nbits       = 1,
  parameter p_shamt_nbits = 1 
) (
  input  logic [      p_nbits-1:0] in,
  input  logic [p_shamt_nbits-1:0] shamt,
  output logic [      p_nbits-1:0] out
);

  assign out = (in >> shamt);

endmodule

`endif  /* CMN_ARITHMETIC_V */

`ifndef  fft_helpers_sine_wave_lookup_16_8_32 
`define  fft_helpers_sine_wave_lookup_16_8_32 
// SINE WAVE OF BIT_WIDTH = 16, DECIMAL_PT =  8
// FOR FFT OF SIZE = 32
module fft_helpers_sine_wave_lookup_16_8_32 
   (
       output logic [16 - 1:0] sine_wave_out [0:32 - 1]
   );
   assign sine_wave_out[0] = 0;
   assign sine_wave_out[1] = 50;
   assign sine_wave_out[2] = 98;
   assign sine_wave_out[3] = 142;
   assign sine_wave_out[4] = 181;
   assign sine_wave_out[5] = 213;
   assign sine_wave_out[6] = 237;
   assign sine_wave_out[7] = 251;
   assign sine_wave_out[8] = 256;
   assign sine_wave_out[9] = 251;
   assign sine_wave_out[10] = 237;
   assign sine_wave_out[11] = 213;
   assign sine_wave_out[12] = 181;
   assign sine_wave_out[13] = 142;
   assign sine_wave_out[14] = 98;
   assign sine_wave_out[15] = 50;
   assign sine_wave_out[16] = 0;
   assign sine_wave_out[17] = -50;
   assign sine_wave_out[18] = -98;
   assign sine_wave_out[19] = -142;
   assign sine_wave_out[20] = -181;
   assign sine_wave_out[21] = -213;
   assign sine_wave_out[22] = -237;
   assign sine_wave_out[23] = -251;
   assign sine_wave_out[24] = -256;
   assign sine_wave_out[25] = -251;
   assign sine_wave_out[26] = -237;
   assign sine_wave_out[27] = -213;
   assign sine_wave_out[28] = -181;
   assign sine_wave_out[29] = -142;
   assign sine_wave_out[30] = -98;
   assign sine_wave_out[31] = -50;
endmodule