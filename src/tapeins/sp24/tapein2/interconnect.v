`include "spi/minion.v"
`include "arbiter_router/router.v"
`include "fft/pease/fft.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"
`include "arbiter_router/arbiter.v"
`include "arbiter_router/router.v"
`include "crossbars/blocking_overrideable.v"
`include "classifier/classifier.v"
`include "wishbone/wishbone.v"

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
  // Override each of the xbar inputs/outputs to spi
  input logic input_xbar_input_override,
  input logic input_xbar_output_override,
  input logic classifier_xbar_input_override,
  input logic classifier_xbar_output_override,
  input logic output_xbar_input_override,
  input logic output_xbar_output_override,
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
      $error("XBAR_CTRL_BITS must be less than or equal to DATA_BITS");
    end
  endgenerate

  // INPUT XBAR
  logic [     DATA_BITS-1:0] input_xbar_recv_msg    [3];
  logic                      input_xbar_recv_rdy    [3];
  logic                      input_xbar_recv_val    [3];

  logic [     DATA_BITS-1:0] input_xbar_send_msg    [3];
  logic                      input_xbar_send_rdy    [3];
  logic                      input_xbar_send_val    [3];

  logic [XBAR_CTRL_BITS-1:0] input_xbar_control_msg;
  logic                      input_xbar_control_rdy;
  logic                      input_xbar_control_val;

  crossbars_BlockingOverrideable #(
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
    .control(input_xbar_control_msg),
    .control_rdy(input_xbar_control_rdy),
    .control_val(input_xbar_control_val),
    .input_override(input_xbar_input_override),
    .output_override(input_xbar_output_override)
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

  crossbars_BlockingOverrideable #(
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
    .control_val(classifier_xbar_control_val),
    .input_override(classifier_xbar_input_override),
    .output_override(classifier_xbar_output_override)
  );

  // OUTPUT XBAR
  logic                      output_xbar_recv_msg    [3];
  logic                      output_xbar_recv_rdy    [3];
  logic                      output_xbar_recv_val    [3];

  logic                      output_xbar_send_msg    [3];
  logic                      output_xbar_send_rdy    [3];
  logic                      output_xbar_send_val    [3];

  logic [XBAR_CTRL_BITS-1:0] output_xbar_control_msg;
  logic                      output_xbar_control_rdy;
  logic                      output_xbar_control_val;

  // 1 bit output XBAR with classifier output
  crossbars_BlockingOverrideable #(
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
    .control(output_xbar_control_msg),
    .control_rdy(output_xbar_control_rdy),
    .control_val(output_xbar_control_val),
    .input_override(output_xbar_input_override),
    .output_override(output_xbar_output_override)
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

  serdes_Serializer #(
    .N_SAMPLES(32),
    .BIT_WIDTH(DATA_BITS)
  ) fft_serializer (
    .clk(clk),
    .reset(reset),
    .send_val(classifier_xbar_recv_val[2]),
    .send_rdy(classifier_xbar_recv_rdy[2]),
    .send_msg(classifier_xbar_recv_msg[2]),
    .recv_val(fft_send_val),
    .recv_rdy(fft_send_rdy),
    .recv_msg(fft_send_msg)
  );

  // Deserializer for the classifier, hooked up to output 1 of the classifier crossbar
  logic [DATA_BITS-1:0] classifier_recv_msg [32];
  logic                 classifier_recv_val;
  logic                 classifier_recv_rdy;

  serdes_Deserializer #(
    .N_SAMPLES(32),
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
    .N_SAMPLES (32)
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
    for (genvar i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin
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
    for (genvar i = 0; i <= 9; i = i + 1) begin
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
    for (genvar i = 5; i <= 8; i = i + 1) begin
      assign arbiter_msg[i] = 16'b0;
      assign arbiter_val[i] = 1'b0;
    end
  endgenerate

  // 9: loopback to arbiter
  // 10+: unused
  generate
    for (genvar i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin
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
