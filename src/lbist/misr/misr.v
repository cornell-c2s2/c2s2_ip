// ===================================================================
// Author: Johnny Martinez
// Date: 10/23/2024
// Documentation: https://confluence.cornell.edu/display/c2s2/MISR
//
// Spec: Val/Rdy MISR implementation. Takes in from the lbist
// controller the expected number of inputs from the CUT to hash.
// Reads the outputs of the CUT and hashes them together to form
// a unique signature. Returns generated signature to the lbist
// controller. IMPORTANT: Too small of a starting seed can lead to ALIASING
//
// PARAMETERS --------------------------------------------------------
// - CUT_MSG_BITS: Bitwidth of CUT outputs
// - SIGNATURE_BITS: Max number of bits of seed
// - MAX_OUTPUTS_TO_HASH: The max number of inputs to hash
// - SEED: Seed of MISR
// - LBIST_MSG_BITS: Size of the message from lbist controller
//
// I/O ---------------------------------------------------------------
// - clk
// - reset
// - cut_req_val: Valid packet from CUT to hash
// - cut_req_msg: Packet from CUT
// - cut_req_rdy: MISR ready to receive packet from CUT
// - lbist_req_val: Valid request to begin hashing from LBIST Controller
// - lbist_req_msg: Number of inputs to hash together to form the signature
// - lbist_req_rdy: MISR ready to handle another request
// - lbist_resp_val: Valid signature from MISR
// - lbist_resp_msg: Unique signature from MISR
// - lbist_resp_rdy: LBIST Controller ready to receive signature
// ===================================================================

`ifndef MISR_V
`define MISR_V

module misr #(
    parameter int CUT_MSG_BITS = 32,
    parameter int SIGNATURE_BITS = 32,
    parameter int MAX_OUTPUTS_TO_HASH = 32,
    parameter int SEED = 32'd0,
    parameter int LBIST_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH)
    )(
    input logic clk,
    input logic reset,

    // CUT to MISR
    input  logic                      cut_req_val,
    input  logic [CUT_MSG_BITS-1:0]   cut_req_msg,
    output logic                      cut_req_rdy,

    // LBIST CONTROLLER to MISR
    input logic                       lbist_req_val,
    input logic  [LBIST_MSG_BITS:0]   lbist_req_msg,
    output logic                      lbist_req_rdy,

    // MISR to LBIST CONTROLLER
    output logic                      lbist_resp_val,
    output logic [SIGNATURE_BITS-1:0] lbist_resp_msg,
    input  logic                      lbist_resp_rdy
  );

//============================LOCAL_PARAMETERS=================================

  logic [1:0]  state;
  logic [1:0]  next_state;
  logic [$clog2(MAX_OUTPUTS_TO_HASH):0] outputs_hashed;   // Counts number of inputs hashed
  logic [$clog2(MAX_OUTPUTS_TO_HASH):0] outputs_to_hash;  // Number of outputs to be hashed for one signature

  logic [SIGNATURE_BITS - 1:0] signature;                     // Initialized to "SEED" parameter
  logic [SIGNATURE_BITS - 1:0] next_signature;

  // State macros
  localparam [1:0]  IDLE = 2'b00;
  localparam [1:0]  HASH = 2'b01;
  localparam [1:0]  DONE = 2'b10;

//================================DATAPATH=====================================
  assign next_signature = (signature^cut_req_msg);
  always_ff @(posedge clk) begin
    if( reset ) begin
      outputs_hashed  <= '0;
      outputs_to_hash <= '0;
      signature       <= '0;
    end
    else begin
      if( state == IDLE) begin
        signature       <= SEED;
        outputs_to_hash <= lbist_req_msg;
      end
      else if( cut_req_val && state == HASH ) begin
        signature       <= {next_signature[SIGNATURE_BITS-2:0],next_signature[SIGNATURE_BITS-1]};
        outputs_hashed  <= outputs_hashed + 1;
      end
      else if (state == DONE) begin
        outputs_hashed  <= 0;
      end
    end
  end

//===============================CTRL_LOGIC====================================
  always_ff @(posedge clk) begin
    if( reset ) begin
      state <= IDLE;
    end
    else begin
      state <= next_state;
    end
  end

  // State transition logic
  always_comb begin
  case ( state )
    IDLE: if( lbist_req_val ) next_state = HASH;
          else next_state = IDLE;

    HASH: if( outputs_hashed < outputs_to_hash - 1) next_state = HASH;
          else next_state = DONE;

    DONE: if( lbist_resp_rdy ) next_state = IDLE;
          else next_state = DONE;

  default: begin next_state = IDLE; end
  endcase
  end

  // Control signal logic
  always_comb begin
  case ( state )
    IDLE: begin
      cut_req_rdy = 0;             // MISR is not ready to receive packet from CUT in IDLE
      lbist_req_rdy = 1;           // MISR is ready to handle a request from LBIST Controller in IDLE
      lbist_resp_val = 0;          // Output to LBIST Controller is not valid in IDLE
      lbist_resp_msg = '0;         // Output signature is a don't care in IDLE
    end

    HASH: begin
      cut_req_rdy = 1;             // MISR is ready to receive packet from CUT in HASH
      lbist_req_rdy = 0;           // MISR is not ready to handle a request from LBIST Controller in HASH
      lbist_resp_val = 0;          // Output to LBIST Controller is not valid in HASH
      lbist_resp_msg = '0;         // Output signature is a don't care in HASH
    end

    DONE: begin
      cut_req_rdy = 0;             // MISR is not ready to receive packet from CUT in DONE
      lbist_req_rdy = 0;           // MISR is not ready to handle a request from LBIST Controller in DONE
      lbist_resp_val = 1;          // Output to LBIST Controller is valid in DONE
      lbist_resp_msg = signature;  // Output signature set to final hash
    end

    // Same as IDLE
    default: begin
      cut_req_rdy = 0;
      lbist_req_rdy = 1;
      lbist_resp_val = 0;
      lbist_resp_msg = '0;
    end
  endcase
  end

endmodule
`endif /* MISR_V */
