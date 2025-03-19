`include "systolic/SyncFIFO.v"
`include "systolic/SystolicPE.v"

`ifndef SYSTOLICDPATH_V
`define SYSTOLICDPATH_V

module SystolicDpath
#(
  parameter size  = 16,
  parameter nbits = 16,
  parameter dbits = 8
)(
  input  logic                    clk,
  input  logic                    rst,
  input  logic [nbits-1:0]        t_w_in   [size],
  input  logic [nbits-1:0]        l_x_in   [size],
  input  logic                    fifo_wen [size],
  input  logic                    fifo_ren [size],
  input  logic                    mac_en,
  input  logic [$clog2(size)-1:0] out_rsel,
  input  logic [$clog2(size)-1:0] out_csel,
  output logic [nbits-1:0]        b_s_out
  output logic                    x_fifo_full  [size],
  output logic                    x_fifo_empty [size],
  output logic                    w_fifo_full  [size],
  output logic                    w_fifo_empty [size]
);

  genvar i, j;

  // Interal Data Flow Wires

  logic [nbits-1:0] w [size+1][size];
  logic [nbits-1:0] x [size][size+1];
  logic [nbits-1:0] s [size][size];

  // Tensor FIFO

  logic _x_fifo_full  [size];
  logic _x_fifo_empty [size];

  generate
    for(i = 0; i < size; i++) begin : g_tensor_fifo
      SyncFIFO #(size, nbits) TensorFIFO
      (
        .clk   (clk),
        .rst   (rst),
        .wen   (fifo_wen[i]),
        .ren   (fifo_ren[i]),
        .d     (l_x_in[i]),
        .q     (x[i][0]),
        .full  (_x_fifo_full[i]),
        .empty (_x_fifo_empty[i])
      );
    end
  endgenerate

  assign x_fifo_full  = _x_fifo_full;
  assign x_fifo_empty = _x_fifo_empty;

  // Weight FIFO

  logic _w_fifo_full  [size];
  logic _w_fifo_empty [size];

  generate
    for(j = 0; j < size; j++) begin : g_weight_fifo
      SyncFIFO #(size, nbits) WeightFIFO
      (
        .clk   (clk),
        .rst   (rst),
        .wen   (fifo_wen[j]),
        .ren   (fifo_ren[j]),
        .d     (t_w_in[j]),
        .q     (w[0][j]),
        .full  (_w_fifo_full[j]),
        .empty (_w_fifo_empty[j])
      );
    end
  endgenerate

  assign w_fifo_full  = _w_fifo_full;
  assign w_fifo_empty = _w_fifo_empty;

  // Systolic Array

  generate
    for (i = 0; i < size; i++) begin : g_pe_rows
      for (j = 0; j < size; j++) begin : g_pe_cols
        SystolicPE #(nbits, dbits, 1) PE
        (
          .clk   (clk),
          .rst   (rst),
          .en    (en),
          .x_in  (x[i][j]),
          .w_in  (w[i][j]),
          .x_out (x[i][j+1]),
          .w_out (w[i+1][j]),
          .s_out (s[i][j])
        );
      end
    end
  endgenerate

  // Output Logic

  assign b_s_out = s[out_rsel][out_csel];

endmodule

`endif