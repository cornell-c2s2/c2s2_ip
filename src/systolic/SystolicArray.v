`include "systolic/SystolicCtrl.v"
`include "systolic/SystolicDpath.v"

`ifndef SYSTOLICARRAY_V
`define SYSTOLICARRAY_V

module SystolicArray
#(
  parameter size  = 16,
  parameter nbits = 16,
  parameter dbits = 8
)(
  input  logic                    clk,
  input  logic                    rst,
  
  input  logic [nbits-1:0]        l_x_in,
  input  logic                    l_x_in_val,
  output logic                    l_x_in_rdy,

  input  logic [nbits-1:0]        t_w_in,
  input  logic                    t_w_in_val,
  output logic                    t_w_in_rdy,

  input  logic [$clog2(size)-1:0] out_rsel,
  input  logic [$clog2(size)-1:0] out_csel,
  output logic [nbits-1:0]        b_s_out
);

  logic mac_en;

  logic [$clog2(size)-1:0] x_fifo_sel;
  logic                    x_fifo_wen   [size];
  logic                    x_fifo_ren   [size];
  logic                    x_fifo_full  [size];
  logic                    x_fifo_empty [size];
  
  logic [$clog2(size)-1:0] w_fifo_sel;
  logic                    w_fifo_wen   [size];
  logic                    w_fifo_ren   [size];
  logic                    w_fifo_full  [size];
  logic                    w_fifo_empty [size];

  SystolicArray #(size, nbits, dbits) dpath
  (
    .*
  );



endmodule

`endif