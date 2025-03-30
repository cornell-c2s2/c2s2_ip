`include "systolic/SystolicPE.v"
`include "systolic/SystolicBuffer.v"

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
  input  logic                    mac_en,

  input  logic [nbits-1:0]        l_x_col_in   [size],
  input  logic                    x_fifo_wen   [size],
  input  logic                    x_fifo_ren   [size],
  output logic                    x_fifo_full  [size],
  output logic                    x_fifo_empty [size],

  input  logic [nbits-1:0]        t_w_row_in   [size],
  input  logic                    w_fifo_wen   [size],
  input  logic                    w_fifo_ren   [size],
  output logic                    w_fifo_full  [size],
  output logic                    w_fifo_empty [size],

  input  logic [$clog2(size)-1:0] out_rsel,
  input  logic [$clog2(size)-1:0] out_csel,
  output logic [nbits-1:0]        b_s_out
);

  genvar i, j;

  // Interal Data Flow Wires

  logic [nbits-1:0] w [size+1][size];
  logic [nbits-1:0] x [size][size+1];
  logic [nbits-1:0] s [size][size];

  // Tensor FIFO

  generate
    for(i = 0; i < size; i++) begin : g_tensor_fifo
      SyncFIFO #(size, nbits) TensorFIFO
      (
        .clk   (clk),
        .rst   (rst),
        .wen   (x_fifo_wen[i]),
        .ren   (x_fifo_ren[i]),
        .d     (l_x_col_in[i]),
        .q     (x[i][0]),
        .full  (x_fifo_full[i]),
        .empty (x_fifo_empty[i])
      );
    end
  endgenerate

  // Weight FIFO

  generate
    for(j = 0; j < size; j++) begin : g_weight_fifo
      SyncFIFO #(size, nbits) WeightFIFO
      (
        .clk   (clk),
        .rst   (rst),
        .wen   (w_fifo_wen[i]),
        .ren   (w_fifo_ren[i]),
        .d     (t_w_row_in[i]),
        .q     (w[0][j]),
        .full  (w_fifo_full[j]),
        .empty (w_fifo_empty[j])
      );
    end
  endgenerate

  // Systolic Array

  generate
    for (i = 0; i < size; i++) begin : g_pe_rows
      for (j = 0; j < size; j++) begin : g_pe_cols
        SystolicPE #(nbits, dbits, 1) PE
        (
          .clk   (clk),
          .rst   (rst),
          .en    (mac_en),
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