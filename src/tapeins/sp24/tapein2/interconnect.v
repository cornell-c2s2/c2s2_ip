`include "spi/minion.v"
`include "arbiter_router/router.v"
`include "crossbars/blocking.v"
`include "fft/pease/fft.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"
`include "arbiter_router/arbiter.v"
`include "arbiter_router/router.v"

module tapeins_sp24_tapein1_Interconnect (
  input logic clk,
  input logic reset,
  input logic cs,
  input logic mosi,
  output logic miso,
  input logic sclk,
  output logic minion_parity,
  output logic adapter_parity,
  // These outputs are necessary to set the valid
  // io_oeb and io_out values for the gpios.
  output logic [22:0] io_oeb,
  output logic [4:0] io_out
);
  logic [17:0] spi_recv_msg;
  logic        spi_recv_rdy;
  logic        spi_recv_val;
  logic [17:0] spi_send_msg;
  logic        spi_send_rdy;
  logic        spi_send_val;

  // io_oeb can always be zero as we are using inputs with nopull
  assign io_oeb = 0;
  // gpios 0-4 require output values to be set.
  assign io_out = 0;

  localparam ADDR_BITS = 3;
  localparam ROUTER_ARBITER_SIZE = 1 << ADDR_BITS;
  localparam DATA_BITS = 16;

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
  logic [15:0] arbiter_msg[ROUTER_ARBITER_SIZE];
  logic        arbiter_rdy[ROUTER_ARBITER_SIZE];
  logic        arbiter_val[ROUTER_ARBITER_SIZE];

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

  // INPUT XBAR
  logic [15:0] input_xbar_recv_msg[3];
  logic        input_xbar_recv_rdy[3];
  logic        input_xbar_recv_val[3];

  crossbars_Blocking #(
    .BIT_WIDTH(DATA_BITS),
    .N_INPUTS (3),
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
    .control(input_control_msg),
    .control_rdy(input_control_rdy),
    .control_val(input_control_val)
  );

  // CLASSIFIER XBAR
  logic [15:0] classifier_recv_msg[3];
  logic        classifier_recv_val[3];
  logic        classifier_recv_rdy[3];

  crossbars_Blocking #(
    .BIT_WIDTH(DATA_BITS),
    .N_INPUTS (3),
    .N_OUTPUTS(3)
  ) classifier_xbar (
    .clk(clk),
    .reset(reset),
    .recv_msg(classifier_recv_msg),
    .recv_val(classifier_recv_val),
    .recv_rdy(classifier_recv_rdy),
    .send_msg(classifier_send_msg),
    .send_val(classifier_send_val),
    .send_rdy(classifier_send_rdy),
    .control(classifier_control_msg),
    .control_rdy(classifier_control_rdy),
    .control_val(classifier_control_val)
  );

  // 1 bit output XBAR with classifier output
  crossbars_Blocking #(
    .BIT_WIDTH(1),
    .N_INPUTS (3),
    .N_OUTPUTS(3)
  ) output_xbar (
    .clk(clk),
    .reset(reset),
    .recv_msg(output_xbar_recv_msg),
    .recv_val(output_xbar_recv_val),
    .recv_rdy(output_xbar_recv_rdy),
    .send_msg(output_xbar_send_msg),
    .send_val(output_xbar_send_val),
    .send_rdy(output_xbar_send_rdy),
    .control(output_control_msg),
    .control_rdy(output_control_rdy),
    .control_val(output_control_val)
  );

  // Deserializer for the FFT, hooked up to output 1 of the input crossbar
  logic [15:0] fft_recv_msg [32];
  logic        fft_recv_val;
  logic        fft_recv_rdy;

  serdes_Deserializer #(
    .N_SAMPLES(32),
    .BIT_WIDTH(16)
  ) fft_deserializer (
    .clk(clk),
    .reset(reset),
    .recv_val(input_xbar_send_val[1]),
    .recv_rdy(input_xbar_send_rdy[1]),
    .recv_msg(input_xbar_send_msg[1]),
    .send_val(fft_recv_val),
    .send_rdy(fft_recv_rdy),
    .send_msg(fft_recv_msg)
  );

  // Serializer for the FFT, hooked up to input 1 of the classifier crossbar
  logic [15:0] fft_send_msg [32];
  logic        fft_send_val;
  logic        fft_send_rdy;

  serdes_Serializer #(
    .N_SAMPLES(32),
    .BIT_WIDTH(16)
  ) fft_serializer (
    .clk(clk),
    .reset(reset),
    .send_val(output_xbar_recv_val[1]),
    .send_rdy(output_xbar_recv_rdy[1]),
    .send_msg(output_xbar_recv_msg[1]),
    .recv_val(fft_send_val),
    .recv_rdy(fft_send_rdy),
    .recv_msg(fft_send_msg)
  );

  // Deserializer for the classifier, hooked up to output 1 of the classifier crossbar
  logic [15:0] classifier_recv_msg [32];
  logic        classifier_recv_val;
  logic        classifier_recv_rdy;

  serdes_Deserializer #(
    .N_SAMPLES(32),
    .BIT_WIDTH(16)
  ) classifier_deserializer (
    .clk(clk),
    .reset(reset),
    .recv_val(input_xbar_send_val[1]),
    .recv_rdy(input_xbar_send_rdy[1]),
    .recv_msg(input_xbar_send_msg[1]),
    .send_val(classifier_recv_val),
    .send_rdy(classifier_recv_rdy),
    .send_msg(classifier_recv_msg)
  );

  // always_ff @(posedge clk) begin
  //   $display("%h %h %h %h", output_xbar_recv_val[0], output_xbar_recv_val[1],
  //            output_xbar_send_val[0], output_xbar_send_val[1]);
  // end


  // PEASE FFT
  fft_pease_FFT #(
    .BIT_WIDTH (16),
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

  // 7 inputs:
  // 0: input xbar inject
  // 1: input xbar config
  // 2: classifier xbar inject
  // 3: classifier xbar config
  // 4: output xbar inject
  // 5: output xbar config
  // 6: classifier config

  // 5 outputs:
  // 0: input xbar output
  // 1: unused
  // 2: classifier xbar output
  // 3: unused
  // 4: output xbar output

endmodule
