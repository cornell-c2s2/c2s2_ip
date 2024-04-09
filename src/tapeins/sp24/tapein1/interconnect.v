`include "spi/minion.v"

module tapeins_sp24_tapein1_Interconnect (
  input  logic clk,
  input  logic reset,
  input  logic cs,
  input  logic mosi,
  output logic miso,
  input  logic sclk,
);
  spi_Minion #(.nbits(20)) minion (
    
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
endmodule
