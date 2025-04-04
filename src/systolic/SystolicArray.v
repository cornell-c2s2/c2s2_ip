`include "serdes/deserializer.v"
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

  input  logic [nbits-1:0]        l_x_in,
  input  logic                    x_recv_val,
  output logic                    x_recv_rdy,

  input  logic [nbits-1:0]        t_w_in,
  input  logic                    w_recv_val,
  output logic                    w_recv_rdy,

  input  logic [$clog2(size)-1:0] out_rsel,
  input  logic [$clog2(size)-1:0] out_csel,
  output logic [nbits-1:0]        b_s_out
);

  //================================================
  // Tensor Deserializer (CMO)
  //================================================

  logic x_send_val;
  logic x_send_rdy;

  logic [nbits-1:0] l_x_col_in [size];

  serdes_Deserializer #(
    .N_SAMPLES (size),
    .BIT_WIDTH (nbits)
  ) x_des (
    .clk      (clk),
    .reset    (rst),
    .recv_val (x_recv_val),
    .recv_rdy (x_recv_rdy),
    .recv_msg (l_x_in),
    .send_val (x_send_val),
    .send_rdy (x_send_rdy),
    .send_msg (l_x_col_in)
  );

  //================================================
  // Weight Deserializer (RMO)
  //================================================

  logic w_send_val;
  logic w_send_rdy;

  logic [nbits-1:0] t_w_row_in [size];

  serdes_Deserializer #(
    .N_SAMPLES (size),
    .BIT_WIDTH (nbits)
  ) w_des (
    .clk      (clk),
    .reset    (rst),
    .recv_val (w_recv_val),
    .recv_rdy (w_recv_rdy),
    .recv_msg (t_w_in),
    .send_val (w_send_val),
    .send_rdy (w_send_rdy),
    .send_msg (t_w_row_in)
  );

  //================================================
  // Systolic Array (Data Path)
  //================================================

  logic mac_en;

  logic x_fifo_wen   [size];
  logic x_fifo_ren   [size];
  logic x_fifo_full  [size];
  logic x_fifo_empty [size];

  logic w_fifo_wen   [size];
  logic w_fifo_ren   [size];
  logic w_fifo_full  [size];
  logic w_fifo_empty [size];

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