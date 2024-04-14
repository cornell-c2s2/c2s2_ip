`include "spi/minion.v"
`include "arbiter_router/router.v"
`include "crossbars/blocking.v"
`include "fft/pease/fft.v"

module tapeins_sp24_tapein1_Interconnect (
  input  logic clk,
  input  logic reset,
  input  logic cs,
  input  logic mosi,
  output logic miso,
  input  logic sclk
);
  logic [17:0] spi_recv_msg;
  logic        spi_recv_rdy;
  logic        spi_recv_val;
  logic [17:0] spi_send_msg;
  logic        spi_send_rdy;
  logic        spi_send_val;

  // SPI MINION
  spi_Minion #(
    .nbits(18)
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

  // ROUTER
  logic [17:0] router_msg [4];
  logic        router_rdy [4];
  logic        router_val [4];

  arbiter_router_Router #(
    .nbits(18),
    .noutputs(4)
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
  logic [17:0] arbiter_msg [2];
  logic        arbiter_rdy [2];
  logic        arbiter_val [2];

  arbiter_router_Arbiter #(
    .nbits(18),
    .ninputs(2),
    .addr_nbits(2)
  ) arbiter (
    .clk(clk),
    .reset(reset),
    .istream_val(arbiter_val),
    .istream_msg(arbiter_msg),
    .istream_rdy(arbiter_rdy),
    .ostream_val(spi_send_val),
    .ostream_msg(spi_send_msg),
    .ostream_rdy(spi_send_rdy)
  );

  // INPUT XBAR
  logic [15:0] input_xbar_recv_msg[1];
  logic        input_xbar_recv_rdy[1];
  logic        input_xbar_recv_val[1];

  // input 0 is SPI at address 0
  assign input_xbar_recv_msg[0] = router_msg[0][15:0];
  assign input_xbar_recv_val[0] = router_val[0];
  assign input_xbar_recv_rdy[0] = router_rdy[0];

  logic [15:0] input_xbar_send_msg[2];
  logic        input_xbar_send_rdy[2];
  logic        input_xbar_send_val[2];

  // output 0 is SPI at address 0
  assign input_xbar_send_msg[0] = arbiter_msg[0][15:0];
  assign input_xbar_send_val[0] = arbiter_val[0];
  assign input_xbar_send_rdy[0] = arbiter_rdy[0];
  
  // configuration message for the crossbar
  // 1 bit wide because there are 2 possible configs
  logic        input_control_msg;
  logic        input_control_rdy;
  logic        input_control_val;
  // hooked up to address 2
  assign input_control_msg = router_msg[2][0];
  assign input_control_rdy = router_rdy[2];
  assign input_control_val = router_val[2];

  crossbars_Blocking #(
    .BIT_WIDTH(16),
    .N_INPUTS(1), // for now, just SPI
    .N_OUTPUTS(2) // SPI and FFT
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
    .control_rdy(input_control_val)
  );
  
  // PEASE FFT
  logic fft_send_msg;
  logic fft_send_val;
  logic fft_send_rdy;

  fft_pease_FFT #(
    .BIT_WIDTH(32),
    .DECIMAL_PT(16),
    .N_SAMPLES(8)
  ) fft (
    .reset(reset),
    .clk(clk),
    .recv_msg(input_xbar_send_msg),
    .recv_val(input_xbar_send_val),
    .recv_rdy(input_xbar_send_rdy),
    .send_msg(fft_send_msg),
    .send_val(fft_send_val),
    .send_rdy(fft_send_rdy)
);

  // OUTPUT XBAR
  logic [15:0] output_xbar_recv_msg[2];
  logic        output_xbar_recv_rdy[2];
  logic        output_xbar_recv_val[2];

  // input 0 is SPI at address 1
  assign output_xbar_recv_msg[0] = router_msg[1][15:0];
  assign output_xbar_recv_val[0] = router_val[1];
  assign output_xbar_recv_rdy[0] = router_rdy[1];
  
  logic [15:0] output_xbar_send_msg[1];
  logic        output_xbar_send_rdy[1];
  logic        output_xbar_send_val[1];

  // output 0 is SPI at address 1
  assign output_xbar_send_msg[0] = arbiter_msg[1][15:0];
  assign output_xbar_send_val[0] = arbiter_val[1];
  assign output_xbar_send_rdy[0] = arbiter_rdy[1];

  // configuration message for the crossbar
  // 2 bits wide because there are 4 possible configs
  logic        output_control_msg;
  logic        output_control_rdy;
  logic        output_control_val;

  // hooked up to address 3
  assign output_control_msg = router_msg[3][0];
  assign output_control_rdy = router_rdy[3];
  assign output_control_val = router_val[3];

  crossbars_Blocking #(
    .BIT_WIDTH(16),
    .N_INPUTS(2), // for now, just SPI and FFT
    .N_OUTPUTS(1) // for now, just SPI
  ) output_xbar (
    .clk(clk),
    .reset(reset),
    .recv_msg(output_xbar_recv_msg),
    .recv_val(output_xbar_recv_val),
    .recv_rdy(output_xbar_recv_rdy),
    .send_msg(output_xbar_send_msg),
    .send_val(output_xbar_send_val),
    .send_rdy(output_xbar_send_rdy),
    .control(control_msg),
    .control_rdy(control_rdy),
    .control_rdy(control_val)
  );

endmodule
