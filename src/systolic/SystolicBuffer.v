`include "cmn/demuxes.v"
`include "systolic/SyncFIFO.v"

`ifndef SYSTOLICBUFFER_V
`define SYSTOLICBUFFER_V

module SystolicBuffer
#(
  parameter size  = 16,
  parameter nbits = 16
)(
  input  logic                    clk,
  input  logic                    rst,
  input  logic [nbits-1:0]        d,
  input  logic [$clog2(size)-1:0] sel,
  input  logic                    wen   [size],
  input  logic                    ren   [size],
  output logic                    full  [size],
  output logic                    empty [size],
  output logic [nbits-1:0]        out   [size]
);

  logic [nbits-1:0] demux_out [size];

  cmn_DemuxN #(
    .nbits    (nbits),
    .noutputs (size)
  ) demux (
    .in  (d),
    .sel (sel),
    .out (demux_out)
  );

  genvar i;
  generate
    for(i = 0; i < size; i++) begin : g_fifo
      SyncFIFO #(size, nbits) fifo
      (
        .clk   (clk),
        .rst   (rst),
        .wen   (wen[i]),
        .ren   (ren[i]),
        .d     (demux_out[i]),
        .q     (out[i]),
        .full  (full[i]),
        .empty (empty[i])
      );
    end
  endgenerate

endmodule

`endif