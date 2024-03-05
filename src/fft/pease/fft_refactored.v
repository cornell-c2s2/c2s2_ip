`ifndef PEASE_FFT_V2
`define PEASE_FFT_V2

`include "cmn/regfiles.v"
`include "fixed_point/combinational/butterflyAlt.v"

module fft_pease_FFT_V2 #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8,
  parameter int N_BTRFLY   = 2
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg,
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic                   send_val,
  input  logic                   send_rdy,

  input logic reset,
  input logic clk
);

  //------------------------------------------------------------------------
  // FSM Ctrl
  //------------------------------------------------------------------------

  logic [2:0] state, next_state;
  localparam int N_FFT_STG = $clog2(N_SAMPLES);

  //------------------------------------------------------------------------
  // Shared Registers for storing FFT data
  //------------------------------------------------------------------------

  // Read and write data
  logic [BIT_WIDTH * 2 - 1:0] read_data0, read_data1;
  logic [BIT_WIDTH * 2 - 1:0] write_data0, write_data1;

  // Read and write addr
  logic [N_FFT_STG - 1:0] read_addr0, read_addr1;
  logic [N_FFT_STG - 1:0] write_addr0, write_addr1;

  // Write enable
  logic write_en0, write_en1;

  // Regfile for real data
  // Upper BIT_WIDTH bits are real data, lower BIT_WIDTH bits are imaginary
  cmn_Regfile_2r2w #(
    .p_data_nbits (BIT_WIDTH * 2),
    .p_num_entries(N_SAMPLES)
  ) real_regfile (
    .*
  );

  //------------------------------------------------------------------------
  // Butterfly Unit
  //------------------------------------------------------------------------





endmodule


`endif
