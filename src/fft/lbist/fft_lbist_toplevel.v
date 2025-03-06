`ifndef FFT_LBIST_TOPLEVEL_V
`define FFT_LBIST_TOPLEVEL_V

`include "lbist/lbist_controller/lbist_controller.v"
`include "lbist/lfsr/lfsr.v"
`include "lbist/misr/misr.v"
`include "fft/pease/fft.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"

module fft_lbist_toplevel #(
  parameter int SEED_BITS = 32,
  parameter int SIGNATURE_BITS = 16,
  parameter int FFT_ARRAY_LENGTH = 4,
  parameter int NUM_SEEDS = 8,           // Increment if adding new seed
  parameter int NUM_HASHES = 80,
  parameter int MAX_OUTPUTS_TO_HASH = 100,
  parameter int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH),
  parameter int DECIMAL_PT = 4,
  parameter [SEED_BITS-1:0] LFSR_SEEDS [NUM_SEEDS-1:0] = {
    32'b10101110100101100000101111000010,
    32'b10000111001110100111100001011100,
    32'b10001111101000100111111010010111,
    32'b10111010000110110000000000110111,
    32'b11010011001001101011100100010101,
    32'b01100101110011011100001001101000,
    32'b10100011101101000101010111100011,
    32'b11011100011010111001110000101001
  },
  parameter [SIGNATURE_BITS-1:0] EXPECTED_SIGNATURES [NUM_SEEDS-1:0] = {
      16'b1100111001111011,
      16'b1100101001001101,
      16'b1001011011010011,
      16'b0100110110111010,
      16'b1010110001010011,
      16'b1101000101011111,
      16'b1101010001100010,
      16'b1000111010101101
  }
  )(
  input logic clk,
  input logic reset,

  input  logic                   lbist_req_val,
  output logic                   lbist_req_rdy,

  output logic                   lbist_resp_val,
  output logic [NUM_SEEDS-1:0]   lbist_resp_msg,
  input  logic                   lbist_resp_rdy
  );

  // Controller to LFSR, sends seed
  logic                      ctrl_lfsr_resp_val;
  logic [SEED_BITS-1:0]      ctrl_lfsr_resp_msg;
  logic                      ctrl_lfsr_resp_rdy;

  // Controller to MISR, sends number of outputs to hash
  logic                      ctrl_misr_req_val;
  logic [MISR_MSG_BITS:0]    ctrl_misr_req_msg;
  logic                      ctrl_misr_req_rdy;

  // MISR to controller, sends hash
  logic                      misr_ctrl_resp_val;
  logic [SIGNATURE_BITS:0]   misr_ctrl_resp_msg;
  logic                      misr_ctrl_resp_rdy;

  logic                      lfsr_deser_resp_val;
  logic [SEED_BITS-1:0]      lfsr_deser_resp_msg;
  logic                      lfsr_deser_resp_rdy;

  logic                      deser_fft_resp_val;
  logic [SEED_BITS-1:0]      deser_fft_resp_msg [FFT_ARRAY_LENGTH-1:0];
  logic                      deser_fft_resp_rdy;

  logic                      fft_ser_resp_val;
  logic [SEED_BITS-1:0]      fft_ser_resp_msg [FFT_ARRAY_LENGTH-1:0];
  logic                      fft_ser_resp_rdy;

  logic                      ser_misr_resp_val;
  logic [SEED_BITS-1:0]      ser_misr_resp_msg;
  logic                      ser_misr_resp_rdy;

  // Controller to LFSR and CUT, sends reset signal once outputs have been hashed
  logic                      lfsr_cut_reset;

  lbist_controller #(
    .SEED_BITS          (SEED_BITS),
    .SIGNATURE_BITS     (SIGNATURE_BITS),
    .NUM_SEEDS          (NUM_SEEDS),
    .NUM_HASHES         (NUM_HASHES),
    .MAX_OUTPUTS_TO_HASH(MAX_OUTPUTS_TO_HASH),
    .MISR_MSG_BITS      (MISR_MSG_BITS),
    .LFSR_SEEDS         (LFSR_SEEDS),
    .EXPECTED_SIGNATURES(EXPECTED_SIGNATURES)
  ) lbist_controller (
    .clk           (clk),
    .reset         (reset),
    .lbist_req_val (lbist_req_val),
    .lbist_req_rdy (lbist_req_rdy),
    .lbist_resp_val(lbist_resp_val),
    .lbist_resp_msg(lbist_resp_msg),
    .lbist_resp_rdy(lbist_resp_rdy),
    .lfsr_resp_val (ctrl_lfsr_resp_val),
    .lfsr_resp_msg (ctrl_lfsr_resp_msg),
    .lfsr_resp_rdy (ctrl_lfsr_resp_rdy),
    .lfsr_cut_reset(lfsr_cut_reset),
    .misr_req_val  (ctrl_misr_req_val),
    .misr_req_msg  (ctrl_misr_req_msg),
    .misr_req_rdy  (ctrl_misr_req_rdy),
    .misr_resp_val (misr_ctrl_resp_val),
    .misr_resp_msg (misr_ctrl_resp_msg),
    .misr_resp_rdy (misr_ctrl_resp_rdy)
  );

  lfsr_paramver2 #(
    .LFSR_MSG_BITS(SEED_BITS)
  ) lfsr_paramver2 (
    .clk     (clk),
    .reset   (reset || lfsr_cut_reset),
    .req_val (ctrl_lfsr_resp_val),
    .req_msg (ctrl_lfsr_resp_msg),
    .req_rdy (ctrl_lfsr_resp_rdy),
    .resp_rdy(lfsr_deser_resp_rdy),
    .resp_val(lfsr_deser_resp_val),
    .resp_msg(lfsr_deser_resp_msg)
  );

  serdes_Deserializer #(
    .N_SAMPLES(FFT_ARRAY_LENGTH),
    .BIT_WIDTH(SEED_BITS)
  ) serdes_Deserializer (
    .clk     (clk),
    .reset   (reset || lfsr_cut_reset),
    .recv_val(lfsr_deser_resp_val),
    .recv_rdy(lfsr_deser_resp_rdy),
    .recv_msg(lfsr_deser_resp_msg),
    .send_val(deser_fft_resp_val),
    .send_rdy(deser_fft_resp_rdy),
    .send_msg(deser_fft_resp_msg)
  );

  fft_pease_FFT #(
    .BIT_WIDTH(SEED_BITS),
    .DECIMAL_PT(DECIMAL_PT),
    .N_SAMPLES(FFT_ARRAY_LENGTH)
  ) fft_pease_FFT (
    .clk     (clk),
    .reset   (reset || lfsr_cut_reset),
    .recv_msg(deser_fft_resp_msg),
    .recv_val(deser_fft_resp_val),
    .recv_rdy(deser_fft_resp_rdy),
    .send_msg(fft_ser_resp_msg),
    .send_val(fft_ser_resp_val),
    .send_rdy(fft_ser_resp_rdy)
  );

  serdes_Serializer #(
    .N_SAMPLES(FFT_ARRAY_LENGTH),
    .BIT_WIDTH(SEED_BITS)
  ) serdes_Serializer (
    .clk     (clk),
    .reset   (reset || lfsr_cut_reset),
    .recv_val(fft_ser_resp_val),
    .recv_rdy(fft_ser_resp_rdy),
    .recv_msg(fft_ser_resp_msg),
    .send_val(ser_misr_resp_val),
    .send_rdy(ser_misr_resp_rdy),
    .send_msg(ser_misr_resp_msg)
  );

  misr #(
    .CUT_MSG_BITS       (SIGNATURE_BITS),
    .SIGNATURE_BITS     (SIGNATURE_BITS),
    .MAX_OUTPUTS_TO_HASH(MAX_OUTPUTS_TO_HASH),
    .LBIST_MSG_BITS     (MISR_MSG_BITS),
    .SEED               ('0)
  ) misr (
    .clk           (clk),
    .reset         (reset),
    .cut_req_val   (ser_misr_resp_val),
    .cut_req_msg   (ser_misr_resp_msg[SIGNATURE_BITS - 1:0]),
    .cut_req_rdy   (ser_misr_resp_rdy),
    .lbist_req_val (ctrl_misr_req_val),
    .lbist_req_msg (ctrl_misr_req_msg),
    .lbist_req_rdy (ctrl_misr_req_rdy),
    .lbist_resp_val(misr_ctrl_resp_val),
    .lbist_resp_msg(misr_ctrl_resp_msg),
    .lbist_resp_rdy(misr_ctrl_resp_rdy)
  );

endmodule
`endif /* FFT_LBIST_TOPLEVEL_V */

