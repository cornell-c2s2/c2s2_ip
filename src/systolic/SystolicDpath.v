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
);

  genvar i, j;

  // Interal Data Flow Wires

  logic [nbits-1:0] w [size+1][size];
  logic [nbits-1:0] x [size][size+1];
  logic [nbits-1:0] s [size][size];

  // Tensor FIFO

  logic tensor_fifo_full;
  logic tensor_fifo_empty;

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
        .full  (tensor_fifo_full),
        .empty (tensor_fifo_empty)
      );
    end
  endgenerate

  // Weight FIFO

  logic weight_fifo_full;
  logic weight_fifo_empty;

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
        .full  (weight_fifo_full),
        .empty (weight_fifo_empty)
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