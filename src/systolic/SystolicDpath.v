`include "systolic/SystolicPE.v"

`ifndef SYSTOLICDPATH_V
`define SYSTOLICDPATH_V

module SystolicDpath
#(
  parameter size = 3,
  parameter n = 16,
  parameter d = 8
)(
  input  logic                    clk,
  input  logic                    rst,
  input  logic                    en,
  input  logic [n-1:0]            t_w_in [size],
  input  logic [n-1:0]            l_x_in [size],
  input  logic [$clog2(size)-1:0] out_rsel,
  input  logic [$clog2(size)-1:0] out_csel,
  output logic [n-1:0]            b_s_out
);

logic [n-1:0] w [size+1][size];
logic [n-1:0] x [size][size+1];
logic [n-1:0] s [size][size];

genvar i, j;

generate
  for (j = 0; j < size; j++) begin : g_first_row
    assign w[0][j] = t_w_in[j];
  end
endgenerate
generate
  for (i = 0; i < size; i++) begin : g_first_col
    assign x[i][0] = l_x_in[i];
  end
endgenerate

generate
  for (i = 0; i < size; i++) begin : g_row
    for (j = 0; j < size; j++) begin : g_cols
      SystolicPE #(n, d, 1) PE
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

assign b_s_out = s[out_rsel][out_csel];

endmodule

`endif