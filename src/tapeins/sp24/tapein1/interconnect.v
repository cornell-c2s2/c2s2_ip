`include "spi/minion.v"
`include "arbiter_router/router.v"
`include "crossbars/blocking.v"
`include "fft/pease/fft.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"
`include "arbiter_router/arbiter.v"
`include "arbiter_router/router.v"

module tapeins_sp24_tapein1_Interconnect (
  input  logic clk,
  input  logic reset,
  input  logic cs,
  input  logic mosi,
  output logic miso,
  input  logic sclk,
  output logic minion_parity,
  output logic adapter_parity
);
  logic [17:0] spi_recv_msg;
  logic        spi_recv_rdy;
  logic        spi_recv_val;
  logic [17:0] spi_send_msg;
  logic        spi_send_rdy;
  logic        spi_send_val;

  // SPI MINION
  spi_Minion #(
    .BIT_WIDTH(18),
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
  // Test for SPI (Counter Delayed Response)
  // src:  [msg1, msg2, msg3, msg4, ...]
  // sink: [0x2CAFE, 0x2CAFE, 0x2CAFE, 0x2CAFE, ...]
  //============================================================================

  // logic [5:0] counter;
  // logic val;
  // logic out;

  // assign spi_recv_msg = 18'h2CAFE;
  // assign spi_recv_val = out;
  // assign spi_send_rdy = !val;

  // always_ff @(posedge clk) begin
  //   if (reset) begin
  //     counter <= 6'b0;
  //     val <= 1'b0;
  //     out <= 1'b0;
  //   end else begin
  //     if (val) begin
  //       if (counter == 6'd10) begin
  //         counter <= 6'b0;
  //         out <= 1;
  //       end else begin
  //         counter <= counter + 1;
  //       end
  //     end
  //     if (spi_recv_val && spi_recv_rdy) begin
  //       out <= 0;
  //       val <= 0;
  //     end
  //     if (spi_send_val && spi_send_rdy) begin
  //       val <= 1;
  //     end
  //   end
  // end

  //============================================================================
  // Test for SPI (Loopback)
  // src:  [msg1, msg2, msg3, msg4, ...]
  // sink: [msg1, msg2, msg3, msg4, ...]
  //============================================================================

  // logic cache_val;
  // logic [17:0] cached_msg;
  // assign spi_recv_msg = cached_msg;
  // assign spi_recv_val = cache_val;
  // assign spi_send_rdy = !cache_val;

  // always_ff @(posedge clk) begin
  //   if (reset) begin
  //     cache_val <= 1'b0;
  //   end else begin
  //     if (!cache_val && spi_send_val) begin
  //       cache_val  <= 1'b1;
  //       cached_msg <= spi_send_msg;
  //     end else if (cache_val && spi_recv_rdy) begin
  //       cache_val <= 1'b0;
  //     end
  //   end
  // end

  //============================================================================
  // Interconnect 
  //============================================================================

  // ROUTER
  logic [17:0] router_msg[4];
  logic        router_rdy[4];
  logic        router_val[4];

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
  logic [15:0] arbiter_msg[2];
  logic        arbiter_rdy[2];
  logic        arbiter_val[2];

  arbiter_router_Arbiter #(
    .nbits  (16),
    .ninputs(2)
  ) arbiter (
    .clk(clk),
    .reset(reset),
    .istream_val(arbiter_val),
    .istream_msg(arbiter_msg),
    .istream_rdy(arbiter_rdy),
    .ostream_val(spi_recv_val),
    .ostream_msg(spi_recv_msg[16:0]),
    .ostream_rdy(spi_recv_rdy)
  );

  // There is an extra address bit that is never used
  assign spi_recv_msg[17] = 1'b0;

  // INPUT XBAR
  logic [15:0] input_xbar_recv_msg[2];
  logic        input_xbar_recv_rdy[2];
  logic        input_xbar_recv_val[2];

  // input 0 is SPI at address 0
  assign input_xbar_recv_msg[0] = router_msg[0][15:0];
  assign input_xbar_recv_val[0] = router_val[0];
  assign router_rdy[0] = input_xbar_recv_rdy[0];

  // input 0 is unused (for now)
  // TODO: change this to wishbone
  logic unused_input_xbar = &{1'b0, input_xbar_recv_rdy[1], 1'b0};
  assign input_xbar_recv_msg[1] = 16'b0;
  assign input_xbar_recv_val[1] = 1'b0;

  logic [15:0] input_xbar_send_msg[2];
  logic        input_xbar_send_rdy[2];
  logic        input_xbar_send_val[2];

  // output 0 is SPI at address 0
  assign arbiter_msg[0] = input_xbar_send_msg[0];
  assign arbiter_val[0] = input_xbar_send_val[0];
  assign input_xbar_send_rdy[0] = arbiter_rdy[0];

  // configuration message for the crossbar
  // 1 bit wide because there are 2 possible configs
  logic [1:0] input_control_msg;
  logic input_control_rdy;
  logic input_control_val;
  // hooked up to address 2
  assign input_control_msg = router_msg[2][1:0];
  assign input_control_val = router_val[2];
  assign router_rdy[2] = input_control_rdy;

  crossbars_Blocking #(
    .BIT_WIDTH(16),
    .N_INPUTS (2),   // for now, just SPI
    .N_OUTPUTS(2)    // SPI and FFT
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

  // Deserializer for the FFT, hooked up to output 1 of the input crossbar
  logic [15:0] fft_recv_msg [32];
  logic        fft_recv_val;
  logic        fft_recv_rdy;

  serdes_Deserializer #(
    .N_SAMPLES(32),
    .BIT_WIDTH(16)
  ) deserializer (
    .clk(clk),
    .reset(reset),
    .recv_val(input_xbar_send_val[1]),
    .recv_rdy(input_xbar_send_rdy[1]),
    .recv_msg(input_xbar_send_msg[1]),
    .send_val(fft_recv_val),
    .send_rdy(fft_recv_rdy),
    .send_msg(fft_recv_msg)
  );

  // Serializer for the FFT, hooked up to input 1 of the output crossbar
  logic [15:0] fft_send_msg [32];
  logic        fft_send_val;
  logic        fft_send_rdy;

  serdes_Serializer #(
    .N_SAMPLES(32),
    .BIT_WIDTH(16)
  ) serializer (
    .clk(clk),
    .reset(reset),
    .send_val(output_xbar_recv_val[1]),
    .send_rdy(output_xbar_recv_rdy[1]),
    .send_msg(output_xbar_recv_msg[1]),
    .recv_val(fft_send_val),
    .recv_rdy(fft_send_rdy),
    .recv_msg(fft_send_msg)
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

  // OUTPUT XBAR
  logic [15:0] output_xbar_recv_msg[2];
  logic        output_xbar_recv_rdy[2];
  logic        output_xbar_recv_val[2];

  // input 0 is SPI at address 1
  assign output_xbar_recv_msg[0] = router_msg[1][15:0];
  assign output_xbar_recv_val[0] = router_val[1];
  assign router_rdy[1] = output_xbar_recv_rdy[0];

  logic [15:0] output_xbar_send_msg[2];
  logic        output_xbar_send_rdy[2];
  logic        output_xbar_send_val[2];

  // output 0 is SPI at address 1
  assign arbiter_msg[1] = output_xbar_send_msg[0];
  assign arbiter_val[1] = output_xbar_send_val[0];
  assign output_xbar_send_rdy[0] = arbiter_rdy[1];
  // output 1 is unused (for now)
  // TODO: Change this to wishbone
  logic unused_output_xbar = &{1'b0, output_xbar_send_msg[1], output_xbar_send_val[1], 1'b0};
  assign output_xbar_send_rdy[1] = 1'b0;

  // configuration message for the crossbar
  // 2 bits wide because there are 4 possible configs
  logic [1:0] output_control_msg;
  logic       output_control_rdy;
  logic       output_control_val;

  // hooked up to address 3
  assign output_control_msg = router_msg[3][1:0];
  assign output_control_val = router_val[3];
  assign router_rdy[3] = output_control_rdy;

  crossbars_Blocking #(
    .BIT_WIDTH(16),
    .N_INPUTS (2),   // for now, just SPI and FFT
    .N_OUTPUTS(2)    // for now, just SPI
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

endmodule
