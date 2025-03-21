`include "lbist/lfsr/lfsr.v" 

module lfsr_sva #(
  parameter int LFSR_MSG_BITS = 32,
  parameter int T1 = 1,
  parameter int T2 = 5,
  parameter int T3 = 6,
  parameter int T4 = 31
)(
  input logic clk,
  input logic reset,

  // BIST Controller to LFSR
  input logic [LFSR_MSG_BITS-1:0] req_msg,
  input logic                     req_val,
  input logic                     req_rdy,

  // LFSR to CUT
  input logic                     resp_rdy,
  input logic                     resp_val,
  input logic [LFSR_MSG_BITS-1:0] resp_msg
);

  localparam [1:0] IDLE = 2'b00;
  localparam [1:0] GEN_VAL = 2'b01;

  // ==============================================================================
  // LFSR STATE MACHINE
  // These properties describe the state machine transitions and state
  // machine output as described in the confluence page to ensure the interface
  // and control logic is exactly as specified.
  // ==============================================================================

  // STATE MACHINE OUTPUT LOGIC

  // IDLE control signals
  property p_idle_out;
    @(posedge clk) disable iff (reset)
    (lfsr.state == IDLE) |-> (req_rdy && !resp_val && (resp_msg == '0));
  endproperty

  // GEN_VAL control signals
  property p_gen_val_out;
    @(posedge clk) disable iff (reset)
    (lfsr.state == GEN_VAL) |-> (!req_rdy && resp_val);
  endproperty

  // STATE TRANSITION LOGIC

  // IDLE to GEN_VAL
  property p_idle_to_gen_val;
    @(posedge clk) disable iff (reset)
    (lfsr.state == IDLE && req_val) |-> ##1 lfsr.state == GEN_VAL;
  endproperty

  // GEN_VAL remains in GEN_VAL
  property p_gen_val_to_gen_val;
    @(posedge clk) disable iff (reset)
    (lfsr.state == GEN_VAL && !reset) |-> ##1 lfsr.state == GEN_VAL;
  endproperty

  // ==============================================================================
  // LFSR Functionality Properties
  // These properties verify the LFSR functionality - including proper shifting
  // and XORing of the tap bits
  // ==============================================================================

  // Verify Q register properly takes seed in IDLE state
  property p_q_takes_seed;
    @(posedge clk) disable iff (reset)
    (lfsr.state == IDLE && req_val) |-> ##1 (lfsr.state == GEN_VAL && lfsr.Q == $past(req_msg));
  endproperty

  // Verify Q properly shifts when in GEN_VAL state and resp_rdy is high
  property p_q_shifts;
    @(posedge clk) disable iff (reset)
    (lfsr.state == GEN_VAL && resp_rdy) |-> ##1 (lfsr.Q == {$past(lfsr.Q[LFSR_MSG_BITS-2:0]), $past(lfsr.final_tap)});
  endproperty

  // Verify final_tap computation
  property p_final_tap;
    @(posedge clk)
    (lfsr.final_tap == ((lfsr.Q[T2] ^ (lfsr.Q[T3] ^ lfsr.Q[T4])) ^ lfsr.Q[T1]));
  endproperty

  // ==============================================================================
  // Val/rdy properties
  // These properties ensure that the val/rdy signals are stable when asserted
  // ==============================================================================

  // resp_val and resp_msg should be stable when resp_val is asserted but resp_rdy is not
  property p_resp_val_msg_stable;
    @(posedge clk) disable iff (reset)
    resp_val && !resp_rdy |=> $stable(resp_val) && $stable(resp_msg);
  endproperty

  // Assertions
  idle_out:             assert property(p_idle_out);
  gen_val_out:          assert property(p_gen_val_out);
  idle_to_gen_val:      assert property(p_idle_to_gen_val);
  gen_val_to_gen_val:   assert property(p_gen_val_to_gen_val);
  q_takes_seed:         assert property(p_q_takes_seed);
  q_shifts:             assert property(p_q_shifts);
  final_tap:            assert property(p_final_tap);
  resp_val_msg_stable:  assert property(p_resp_val_msg_stable);

endmodule

bind lfsr lfsr_sva u_lfsr_sva (
  .clk(clk),
  .reset(reset),
  .req_msg(req_msg),
  .req_val(req_val),
  .req_rdy(req_rdy),
  .resp_rdy(resp_rdy),
  .resp_val(resp_val),
  .resp_msg(resp_msg)
);