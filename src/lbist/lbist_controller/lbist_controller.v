// ===================================================================
// Author: Arjun Saini
// Date: 
// Spec: 
// ===================================================================

`ifndef LBIST_CONTROLLER_V
`define LBIST_CONTROLLER_V

module lbist_controller #(
    parameter int SIGNATURE_BITS = 32,                    // Max number of bits of seed
    parameter int NUM_HASHES = 8,                         // Number of hashes to test
    parameter int MAX_OUTPUTS_TO_HASH = 32,               // The max number of inputs to hash together
    parameter int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH)
    )(
    input logic clk,
    input logic reset,

    // Requestor to LBIST CONTROLLER
    input  logic                      lbist_req_val,     // Valid request to init LBIST
    output logic                      lbist_req_rdy,     // LBIST Ready to service new LBIST request

    // LBIST CONTROLLER to requestor
    output logic                      lbist_resp_val,    // Valid output
    output logic [NUM_HASHES-1:0]     lbist_resp_msg,    // Binary number where each bit represents a test sequence. 1 means test passed zero otherwise
    input  logic                      lbist_resp_rdy,    // Requestor ready for lbist output

    // LBIST CONTROLLER to LFSR
    output logic                      lfsr_resp_val,     // Valid output
    output logic [SIGNATURE_BITS-1:0] lfsr_resp_msg,     // Seed sent to LFSR
    input  logic                      lfsr_resp_rdy,     // LFSR ready for next seed

    // LBIST CONTROLLER to MISR
    output logic                      misr_req_val,     // Valid number of outputs from CUT to hash
    output logic [MISR_MSG_BITS-1:0]  misr_req_msg,     // Number of outputs from CUT to hash
    input  logic                      misr_req_rdy,     // MISR ready to service new request

    // MISR to LBIST CONTROLLER
    input  logic                      misr_resp_val,    // Signature from MISR is valid
    input  logic [SIGNATURE_BITS-1:0] misr_resp_msg,    // Signature itself
    output logic                      misr_resp_rdy     // LBIST CONTROLLER ready for new signature
  );

//============================LOCAL_PARAMETERS=================================
  localparam [1:0] IDLE = 2'd0, START = 2'd1, COMP_SIG = 2'd2;
  logic [1:0] state, next_state;
  logic [$clog2(NUM_HASHES)-1:0] counter;
  
  logic [NUM_HASHES-1:0] next_lbist_resp_msg;
  logic next_lbist_resp_val;

  logic [SIGNATURE_BITS-1:0] lfsr_seeds [NUM_HASHES-1:0] = {
      32'h0a89687e,
      32'ha87ded5f,
      32'h481c5077,
      32'h81595729,
      32'hffd39769,
      32'h24b05d57,
      32'h9913b1fd,
      32'hd8df8ed2
    };
    
  logic [SIGNATURE_BITS-1:0] expected_signatures [NUM_HASHES-1:0] = {
      32'h2435b217,
      32'hb25e4d4c,
      32'h16307bd1,
      32'h2ced25e0,
      32'hc5145ccb,
      32'h6180254b,
      32'hc329c75c,
      32'h89b9c2ec
    };

//================================DATAPATH=====================================
  always_comb begin
    case (state)
      IDLE: begin
        lbist_req_rdy       = 1;
        next_lbist_resp_val = 0;
        for (int i = 0; i < NUM_HASHES; i++) begin
          next_lbist_resp_msg[i] = 0;
        end
        lfsr_resp_val = 0;
        lfsr_resp_msg = 0;
        misr_req_val  = 0;
        misr_req_msg  = 0;
        misr_resp_rdy = 0;
      end
      START: begin
        lbist_req_rdy       = 0;
        next_lbist_resp_val = 0;
        next_lbist_resp_msg = lbist_resp_msg;
        lfsr_resp_val       = 1;
        lfsr_resp_msg       = lfsr_seeds[counter];
        misr_req_val        = 1;
        misr_req_msg        = MAX_OUTPUTS_TO_HASH;
        misr_resp_rdy       = 1;
      end
      COMP_SIG: begin
        lbist_req_rdy       = 0;
        next_lbist_resp_val = counter == (NUM_HASHES - 1);
        for (int i = 0; i < NUM_HASHES; i++) begin
          if (i == counter) begin
            next_lbist_resp_msg[i] = misr_resp_msg == expected_signatures[i];
          end else begin
            next_lbist_resp_msg[i] = lbist_resp_msg[i];
          end
        end
        lfsr_resp_val = 0;
        lfsr_resp_msg = 0;
        misr_req_val  = 0;
        misr_req_msg  = 0;
        misr_resp_rdy = 0;
      end
      default: begin
      end
    endcase
  end

//===============================CTRL_LOGIC====================================
  always_comb begin
    case (state)
      IDLE: begin
        if (lbist_req_val && lfsr_resp_rdy && misr_req_rdy) next_state = START;
        else next_state = IDLE;
      end
      START: begin
        if (misr_resp_val) next_state = COMP_SIG;
        else next_state = START;
      end
      COMP_SIG: begin
        if (counter != NUM_HASHES - 1) next_state = START;
        else if (lbist_resp_rdy && lbist_resp_val) next_state = IDLE;
        else next_state = COMP_SIG;
      end
      default: begin
      end
    endcase
  end

  // reset logic
  always_ff @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end
  
  // counter logic
  always_ff @(posedge clk) begin
    if (reset || state == IDLE) begin
      counter <= 0;
    end else if (state == COMP_SIG && next_state == START) begin
      counter <= counter + 1;
    end else begin
      counter <= counter;
    end
  end
  
  // lbist_resp_msg and lbist_resp_val logic
  always_ff @(posedge clk) begin
    if (reset) begin
      for (int i = 0; i < NUM_HASHES; i++) begin
        lbist_resp_msg[i] <= 0;
      end
      lbist_resp_val <= 0;
    end else begin
      lbist_resp_msg <= next_lbist_resp_msg;
      lbist_resp_val <= next_lbist_resp_val;
    end
  end


endmodule
`endif /* LBIST_CONTROLLER_V */
