`include "systolic/SystolicCtrl.v"
`include "systolic/SystolicDpath.v"

`ifndef SYSTOLICARRAY_V
`define SYSTOLICARRAY_V

module SystolicArray
#(
  parameter size  = 4,
  parameter nbits = 16,
  parameter dbits = 8
)(
  input  logic                    clk,
  input  logic                    rst,

  input  logic [nbits-1:0]        l_x_col_in [size],
  input  logic                    x_recv_val,
  output logic                    x_recv_rdy,

  input  logic [nbits-1:0]        t_w_row_in [size],
  input  logic                    w_recv_val,
  output logic                    w_recv_rdy,

  output logic                    mac_rdy,
  output logic                    out_rdy,

  input  logic [$clog2(size)-1:0] out_rsel,
  input  logic [$clog2(size)-1:0] out_csel,
  output logic [nbits-1:0]        b_s_out
);

  logic mac_en;

  logic x_fifo_wen   [size];
  logic x_fifo_ren   [size];
  logic x_fifo_full  [size];
  logic x_fifo_empty [size];

  logic w_fifo_wen   [size];
  logic w_fifo_ren   [size];
  logic w_fifo_full  [size];
  logic w_fifo_empty [size];

  logic mac_rdy;
  logic out_rdy;

  SystolicDpath #(size, nbits, dbits) dpath
  (
    .*
  );

  SystolicCtrl #(size) ctrl
  (
    .*
  );

endmodule

`endif