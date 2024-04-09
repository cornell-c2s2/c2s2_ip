`include "spi/minion.v"

module tapeins_sp24_tapein1_Interconnect (
  input  logic clk,
  input  logic reset,
  input  logic cs,
  input  logic mosi,
  output logic miso,
  input  logic sclk
);
  spi_Minion #(
    .nbits(20)
  ) minion (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .mosi(mosi),
    .miso(miso),
    .sclk(sclk)
  );
endmodule
