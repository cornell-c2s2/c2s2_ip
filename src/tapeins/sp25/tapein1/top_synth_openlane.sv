
`include "tapeins/sp25/tapein1/tapein1_sp25_top.v"

module top_synth #(
  parameter int FIFO_ENTRY_BITS = 8
) (
    // Clock and Reset Ports
    `ifdef USE_POWER_PINS
        inout vccd1, // User area 1 1.8V supply
        inout vssd1, // User area 1 digital ground
    `endif

    input  logic  clk,
    input  logic  reset,

    // SPI Minion ports
    input  logic  cs,
    input  logic  mosi,
    output logic  miso,
    input  logic  sclk,
    output logic  minion_parity,
    output logic  adapter_parity,

    // Async FIFO ports
    input  logic                         ext_clk,
    input  logic [FIFO_ENTRY_BITS-1:0]   async_fifo_recv_msg,
    // TODO: Might need to add a debounce here and latch on TOGGLE not val being high...
    input  logic                         async_fifo_recv_val,
    output logic                         async_fifo_recv_rdy
  );



  tapein1_sp25_top #(
    .FIFO_ENTRY_BITS(FIFO_ENTRY_BITS)
  ) top (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .mosi(mosi),
    .miso(miso),
    .sclk(sclk),
    .minion_parity(minion_parity),
    .adapter_parity(adapter_parity),
    .ext_clk(ext_clk),
    .async_fifo_recv_msg(async_fifo_recv_msg),
    .async_fifo_recv_val(async_fifo_recv_val),
    .async_fifo_recv_rdy(async_fifo_recv_rdy)
  );

endmodule

