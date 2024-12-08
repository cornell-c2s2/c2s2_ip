// ===================================================================
// Author: Arjun Saini
// Date: 11/21/24
// Spec:
// PARAMETERS --------------------------------------------------------
//
// I/O ---------------------------------------------------------------
// - clk
// - reset
// ===================================================================

`ifndef LBIST_TOPLEVEL_V
`define LBIST_TOPLEVEL_V

`include "lbist/lbist_controller/lbist_controller.v"
`include "lbist/lfsr/lfsr.v"
`include "lbist/misr/misr.v"
`include "fixed_point/iterative/multiplier.v"

module lbist_toplevel #(
  parameter int SEED_BITS = 32,
  parameter int SIGNATURE_BITS = 16,
  parameter int NUM_SEEDS = 2,
  parameter int NUM_HASHES = 2,
  parameter int MAX_OUTPUTS_TO_HASH = 5,
  parameter int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH),
  parameter [SEED_BITS-1:0] LFSR_SEEDS [NUM_SEEDS-1:0] = {
    32'b10000111001110100111100001011100,
    32'b11101101011001111010101100101101    // First tested
  },
  parameter [SIGNATURE_BITS-1:0] EXPECTED_SIGNATURES [NUM_SEEDS-1:0] = {
    16'b0110010110100011,
    16'b1100110111100010     // First tested
  }
  )(
  input logic clk,
  input logic reset,

  input  logic                   lbist_req_val,
  output logic                   lbist_req_rdy,

  output logic                   lbist_resp_val,
  output logic [NUM_SEEDS-1:0]   lbist_resp_msg,
  // output logic [NUM_HASHES-1:0]   lbist_resp_msg,

  input  logic                   lbist_resp_rdy
  );

  logic                      ctrl_lfsr_resp_val;
  logic [SEED_BITS-1:0]      ctrl_lfsr_resp_msg;
  logic                      ctrl_lfsr_resp_rdy;

  logic                      ctrl_misr_req_val;
  logic [MISR_MSG_BITS:0]    ctrl_misr_req_msg;
  logic                      ctrl_misr_req_rdy;

  logic                      misr_ctrl_resp_val;
  logic [SIGNATURE_BITS-1:0] misr_ctrl_resp_msg;
  logic                      misr_ctrl_resp_rdy;

  logic                      lfsr_cut_resp_val;
  logic [SEED_BITS-1:0]      lfsr_cut_resp_msg;
  logic                      lfsr_cut_resp_rdy;

  logic                      cut_misr_resp_val;
  logic [SIGNATURE_BITS-1:0] cut_misr_resp_msg;
  logic                      cut_misr_resp_rdy;

  logic                      lfsr_reset;

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
    .lfsr_reset    (lfsr_reset),
    .misr_req_val  (ctrl_misr_req_val),
    .misr_req_msg  (ctrl_misr_req_msg),
    .misr_req_rdy  (ctrl_misr_req_rdy),
    .misr_resp_val (misr_ctrl_resp_val),
    .misr_resp_msg (misr_ctrl_resp_msg),
    .misr_resp_rdy (misr_ctrl_resp_rdy)
  );

  lfsr #(
    .N(SEED_BITS)
  ) lfsr (
    .clk     (clk),
    // .reset   (reset),
    .reset   (reset || lfsr_reset),
    .req_val (ctrl_lfsr_resp_val),
    .req_msg (ctrl_lfsr_resp_msg),
    .req_rdy (ctrl_lfsr_resp_rdy),
    .resp_rdy(lfsr_cut_resp_rdy),
    .resp_val(lfsr_cut_resp_val),
    .resp_msg(lfsr_cut_resp_msg)
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
    .cut_req_val   (cut_misr_resp_val),
    .cut_req_msg   (cut_misr_resp_msg),
    .cut_req_rdy   (cut_misr_resp_rdy),
    .lbist_req_val (ctrl_misr_req_val),
    .lbist_req_msg (ctrl_misr_req_msg),
    .lbist_req_rdy (ctrl_misr_req_rdy),
    .lbist_resp_val(misr_ctrl_resp_val),
    .lbist_resp_msg(misr_ctrl_resp_msg),
    .lbist_resp_rdy(misr_ctrl_resp_rdy)
  );

  fixed_point_iterative_Multiplier #(
    .n(SIGNATURE_BITS),
    .d(0),
    .sign(0)
  ) cut (
    .clk     (clk),
    // .reset   (reset),
    .reset   (reset || lfsr_reset),
    .recv_rdy(lfsr_cut_resp_rdy),
    .recv_val(lfsr_cut_resp_val),
    .a       (lfsr_cut_resp_msg[31:16]),
    .b       (lfsr_cut_resp_msg[15:0]),
    .send_rdy(cut_misr_resp_rdy),
    .send_val(cut_misr_resp_val),
    .c       (cut_misr_resp_msg)
  );

endmodule
`endif /* LBIST_TOPLEVEL_V */

