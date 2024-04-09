`include "spi/minion.v"
`include "arbiter_router/router.v"

module tapeins_sp24_tapein1_Interconnect (
  input  logic clk,
  input  logic reset,
  input  logic cs,
  input  logic mosi,
  output logic miso,
  input  logic sclk
);
  logic [BIT_WIDTH - 1:0] recv_msg;
  logic                   recv_rdy;
  logic                   recv_val;
  logic [BIT_WIDTH - 1:0] send_msg;
  logic                   send_rdy;
  logic                   send_val;

  spi_Minion #(
    .nbits(20)
  ) minion (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .mosi(mosi),
    .miso(miso),
    .sclk(sclk),
    .recv_msg(recv_msg),
    .recv_rdy(recv_rdy),
    .recv_val(recv_val),
    .send_msg(send_msg),
    .send_rdy(send_rdy),
    .send_val(send_val),
    .minion_parity(minion_parity),
    .adapter_parity(adapter_parity)

  );

  arbiter_router_Router #(
    .nbits(20),
    .noutputs(2)
  ) router (
    .clk(clk),
    .reset(reset),
    .istream_val(),
    .istream_msg(),
    .istream_rdy(),
    .ostream_val(),
    .ostream_msg(),
    .ostream_rdy()
  );

endmodule
