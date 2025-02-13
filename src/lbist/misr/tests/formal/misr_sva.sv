`include "lbist/misr/misr.v" 

module misr_sva #(
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
  input  logic                      cut_req_rdy,

  // LBIST CONTROLLER to MISR
  input  logic                       lbist_req_val,
  input  logic  [LBIST_MSG_BITS:0]   lbist_req_msg,
  input  logic                      lbist_req_rdy,

  // MISR to LBIST CONTROLLER
  input  logic                      lbist_resp_val,
  input  logic [SIGNATURE_BITS-1:0] lbist_resp_msg,
  input  logic                      lbist_resp_rdy
);

  // add all outputted hashes to a register
  logic [SIGNATURE_BITS-1:0] hashes[MAX_OUTPUTS_TO_HASH-1:0];
  always_ff @(posedge clk) begin
    if (reset) begin
      hashes <= '{default: '0};
    end else if (lbist_resp_val && lbist_resp_rdy) begin
        hashes[lbist_req_msg] <= lbist_resp_msg;
    end
  end



  localparam [1:0]  IDLE = 2'b00;
  localparam [1:0]  HASH = 2'b01;
  localparam [1:0]  DONE = 2'b10;

  // ==============================================================================
  // MISR STATE MACHINE
  // These properties describe the state machine transitions and state
  // machine output as described in the confluence page to ensure the interface
  // and control logic is exactly as specificed.
  // ==============================================================================

  // STATE MACHINE OUTPUT LOGIC

  // IDLE control signals
  property p_idle_out;
    @(posedge clk) disable iff (reset)
    (misr.state == IDLE) |-> (!cut_req_rdy 
                                && lbist_req_rdy 
                                && !lbist_resp_val 
                                && (lbist_resp_msg == '0));
  endproperty

  // HASH control signals
  property p_hash_out;
    @(posedge clk) disable iff (reset)
    (misr.state == HASH) |-> (cut_req_rdy 
                                && !lbist_req_rdy 
                                && !lbist_resp_val 
                                && (lbist_resp_msg == '0));
  endproperty

  // DONE control signals
  property p_done_out;
    @(posedge clk) disable iff (reset)
    (misr.state == DONE) |-> (!cut_req_rdy 
                                && !lbist_req_rdy 
                                && lbist_resp_val);
  endproperty

  // STATE TRANSITION LOGIC

  // IDLE to HASH
  property p_idle_to_hash;
    @(posedge clk) disable iff (reset)
    (misr.state == IDLE && lbist_req_val) |-> ##1 misr.state == HASH;
  endproperty

  // HASH to DONE
  property p_hash_to_done;
    @(posedge clk) disable iff (reset)
    (misr.state == HASH && misr.done_hashing) |-> ##1 misr.state == DONE;
  endproperty

  // DONE to IDLE
  property p_done_to_idle;
    @(posedge clk) disable iff (reset)
    (misr.state == DONE && lbist_resp_rdy) |-> ##1 misr.state == IDLE;
  endproperty

  // ==============================================================================
  // Val/rdy properties
  // These properties ensure that the val/rdy signals are stable when asserted
  // and that corresponding responses are received for a given request.
  // ==============================================================================
  // check that msg is stable while val asserted. val on for 2 cycles because stable
  // always fails if it is on for a single cycle
  property p_lbist_resp_msg_stability;
    @(posedge clk) disable iff (reset)
      lbist_resp_val && $past(lbist_resp_val) |-> $stable(lbist_resp_msg);
  endproperty

  // LBIST Controller response interface
  property p_lbist_resp_val_rdy_stable; // works!
    @(posedge clk) disable iff (reset)
    lbist_resp_val && !lbist_resp_rdy |=> $stable(lbist_resp_val) && $stable(lbist_resp_msg);
  endproperty

  // checks that when MISR gets LBIST 
  property p_lbist_req_gets_cut_rdy;
    @(posedge clk) disable iff (reset)
      lbist_req_val && lbist_req_rdy |-> ##[0:$] cut_req_rdy;
  endproperty

  // Assertions
  idle_out:                     assert property(p_idle_out);
  hash_out:                     assert property(p_hash_out);
  done_out:                     assert property(p_done_out);
  idle_to_hash:                 assert property(p_idle_to_hash);
  hash_to_done:                 assert property(p_hash_to_done);
  done_to_idle:                 assert property(p_done_to_idle);
  lbist_resp_val_rdy_stable:    assert property(p_lbist_resp_val_rdy_stable);
  lbist_resp_msg_stability:     assert property(p_lbist_resp_msg_stability);
  lbist_req_gets_cut_rdy:       assert property(p_lbist_req_gets_cut_rdy);

endmodule

bind misr misr_sva u_misr_sva (
  .clk(clk),
  .reset(reset),
  .cut_req_val(cut_req_val),
  .cut_req_msg(cut_req_msg),
  .cut_req_rdy(cut_req_rdy),
  .lbist_req_val(lbist_req_val),
  .lbist_req_msg(lbist_req_msg),
  .lbist_req_rdy(lbist_req_rdy),
  .lbist_resp_val(lbist_resp_val),
  .lbist_resp_msg(lbist_resp_msg),
  .lbist_resp_rdy(lbist_resp_rdy)
);