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

  input  logic [nbits-1:0]        l_x_in,
  input  logic [$clog2(size)-1:0] x_fifo_sel,
  input  logic                    x_fifo_wen   [size],
  input  logic                    x_fifo_ren   [size],
  output logic                    x_fifo_full  [size],
  output logic                    x_fifo_empty [size],

  input  logic [nbits-1:0]        t_w_in,
  input  logic [$clog2(size)-1:0] w_fifo_sel,
  input  logic                    w_fifo_wen   [size],
  input  logic                    w_fifo_ren   [size],
  output logic                    w_fifo_full  [size],
  output logic                    w_fifo_empty [size],

  input  logic [$clog2(size)-1:0] out_rsel,
  input  logic [$clog2(size)-1:0] out_csel,
  output logic [nbits-1:0]        b_s_out
);

  // Interal Data Flow Wires

  logic [nbits-1:0] x_buffer_out [size];
  logic [nbits-1:0] w_buffer_out [size];

  logic [nbits-1:0] w [size+1][size];
  logic [nbits-1:0] x [size][size+1];
  logic [nbits-1:0] s [size][size];

  // Tensor Buffer

  SystolicBuffer #(size, nbits) x_buffer
  (
    .clk   (clk),
    .rst   (rst),
    .d     (l_x_in),
    .sel   (x_fifo_sel),
    .wen   (x_fifo_wen),
    .ren   (x_fifo_ren),
    .full  (x_fifo_full),
    .empty (x_fifo_empty),
    .out   (x_buffer_out)
  );

  always_comb begin
    for(int k = 0; k < size; k++)
      x[k][0] = x_buffer_out[k];
  end

  // Weight Buffer

  SystolicBuffer #(size, nbits) w_buffer
  (
    .clk   (clk),
    .rst   (rst),
    .d     (t_w_in),
    .sel   (w_fifo_sel),
    .wen   (w_fifo_wen),
    .ren   (w_fifo_ren),
    .full  (w_fifo_full),
    .empty (w_fifo_empty),
    .out   (w_buffer_out)
  );

  always_comb begin
    for(int k = 0; k < size; k++)
      w[0][k] = w_buffer_out[k];
  end

  // Systolic Array

  genvar i, j;
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