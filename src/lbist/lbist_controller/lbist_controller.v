// ===================================================================
// Author: 
// Date: 
// Spec: 
// ===================================================================

`ifndef LBIST_CONTROLLER_V
`define LBIST_CONTROLLER_V

module lbist_controller #(
    parameter int SIGNATURE_BITS = 32,                    // Max number of bits of seed
    parameter int MAX_OUTPUTS_TO_HASH = 32,               // The max number of inputs to hash together
    parameter int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH)
    )(
    input logic clk,
    input logic reset,

    // Requestor to LBIST CONTROLLER
    input  logic                      lbist_req_val,      // Valid request to init LBIST
    output logic                      lbist_req_rdy,      // LBIST Ready to service new LBIST request

    // LBIST CONTROLLER to requestor
    output logic                      lbist_resp_val,     // Valid output
    output logic [MAX_OUTPUTS_TO_HASH -1 : 0] lbist_resp_msg,     // Binary number where each bit represents a test sequence. 1 means test passed zero otherwise
    input  logic                      lbist_resp_rdy,     // Requestor ready for lbist output

    // LBIST CONTROLLER to LFSR
    output logic                       lfsr_resp_val,
    output logic [SIGNATURE_BITS-1:0]  lfsr_resp_msg,
    input  logic                       lfsr_resp_rdy,

    // LBIST CONTROLLER to MISR
    output logic                       misr_req_val,     // Valid number of outputs from CUT to hash
    output logic  [MISR_MSG_BITS-1:0]  misr_req_msg,     // Number of outputs from CUT to hash
    input logic                        misr_req_rdy,     // MISR ready to service new request

    // MISR to LBIST CONTROLLER
    input  logic                       misr_resp_val,    // Signature from MISR is valid
    input  logic  [SIGNATURE_BITS-1:0] misr_resp_msg,    // Signature itself
    output logic                       misr_resp_rdy     // LBIST CONTROLLER ready for new signature
  );

//============================LOCAL_PARAMETERS=================================

//================================DATAPATH=====================================

//===============================CTRL_LOGIC====================================


endmodule
`endif /* LBIST_CONTROLLER_V */
