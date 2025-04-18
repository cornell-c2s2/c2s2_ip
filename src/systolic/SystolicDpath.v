`include "systolic/SyncFIFO.v"
`include "systolic/SystolicPE.v"

`ifndef SYSTOLICDPATH_V
`define SYSTOLICDPATH_V

module SystolicDpath
#(
  parameter SIZE  = 4,
  parameter NBITS = 16,
  parameter DBITS = 8
)(
  input  logic                    clk,
  input  logic                    rst,
  input  logic                    mac_en,

  input  logic [NBITS-1:0]        l_x_col_in   [SIZE],
  input  logic                    x_fifo_wen   [SIZE],
  input  logic                    x_fifo_ren   [SIZE],
  output logic                    x_fifo_full  [SIZE],
  output logic                    x_fifo_empty [SIZE],

  input  logic [NBITS-1:0]        t_w_row_in   [SIZE],
  input  logic                    w_fifo_wen   [SIZE],
  input  logic                    w_fifo_ren   [SIZE],
  output logic                    w_fifo_full  [SIZE],
  output logic                    w_fifo_empty [SIZE],

  input  logic [$clog2(SIZE)-1:0] out_rsel,
  input  logic [$clog2(SIZE)-1:0] out_csel,
  output logic [NBITS-1:0]        b_s_out
);

  genvar i, j;

  // Interal Data Flow Wires

  logic [NBITS-1:0] w [SIZE+1][SIZE];
  logic [NBITS-1:0] x [SIZE][SIZE+1];
  logic [NBITS-1:0] s [SIZE][SIZE];

  // Tensor FIFO

  generate
    for(i = 0; i < SIZE; i++) begin : g_tensor_fifo
      SyncFIFO #(SIZE, NBITS) TensorFIFO
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
    for(j = 0; j < SIZE; j++) begin : g_weight_fifo
      SyncFIFO #(SIZE, NBITS) WeightFIFO
      (
        .clk   (clk),
        .rst   (rst),
        .wen   (w_fifo_wen[j]),
        .ren   (w_fifo_ren[j]),
        .d     (t_w_row_in[j]),
        .q     (w[0][j]),
        .full  (w_fifo_full[j]),
        .empty (w_fifo_empty[j])
      );
    end
  endgenerate

  // Systolic Array

  generate
    for (i = 0; i < SIZE; i++) begin : g_pe_rows
      for (j = 0; j < SIZE; j++) begin : g_pe_cols
        SystolicPE #(NBITS, DBITS, 1) PE
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