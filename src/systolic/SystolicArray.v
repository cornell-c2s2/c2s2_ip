`include "systolic/SystolicCtrl.v"
`include "systolic/SystolicDpath.v"

`ifndef SYSTOLICARRAY_V
`define SYSTOLICARRAY_V

module SystolicArray
#(
  parameter SIZE  = 4,
  parameter NBITS = 16,
  parameter DBITS = 8
)(
  input  logic                    clk,
  input  logic                    rst,

  input  logic [NBITS-1:0]        l_x_col_in [SIZE],
  input  logic                    x_recv_val,
  output logic                    x_recv_rdy,

  input  logic [NBITS-1:0]        t_w_row_in [SIZE],
  input  logic                    w_recv_val,
  output logic                    w_recv_rdy,

  output logic                    mac_rdy,
  output logic                    out_rdy,

  input  logic [$clog2(SIZE)-1:0] out_rsel,
  input  logic [$clog2(SIZE)-1:0] out_csel,
  output logic [NBITS-1:0]        b_s_out
);

  logic mac_en;
  logic out_en;

  logic x_fifo_wen   [SIZE];
  logic x_fifo_ren   [SIZE];
  logic x_fifo_full  [SIZE];
  logic x_fifo_empty [SIZE];

  logic w_fifo_wen   [SIZE];
  logic w_fifo_ren   [SIZE];
  logic w_fifo_full  [SIZE];
  logic w_fifo_empty [SIZE];

  assign out_en = out_rdy;

  SystolicDpath #(SIZE, NBITS, DBITS) dpath
  (
    .*
  );

  SystolicCtrl #(SIZE) ctrl
  (
    .*
  );

endmodule

`endif