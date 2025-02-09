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

/*// validate that all the hashes are the same after a reset
property unique_hashes;
  @(posedge clk)
  disable iff (!reset)
  (lbist_resp_val && lbist_resp_rdy) |-> 
  (hashes[lbist_req_msg] != lbist_resp_msg);
endproperty
*/

property p_idle_to_hash;
  @(posedge clk) disable iff (reset)
    ( (!cut_req_rdy && lbist_req_rdy && !lbist_resp_val && lbist_req_val) )
      |-> ##1 ( (cut_req_rdy && !lbist_req_rdy && !lbist_resp_val) );
endproperty

assert property (p_idle_to_hash);


// Val/Rdy Properties
  // CUT interface
  property cut_val_rdy_stable;
    @(posedge clk) disable iff (reset)
    cut_req_val && !cut_req_rdy |=> $stable(cut_req_val) && $stable(cut_req_msg);
  endproperty

  property cut_msg_stable;
    @(posedge clk) disable iff (reset)
    cut_req_val |-> $stable(cut_req_msg);
  endproperty

  // LBIST Controller request interface
  property lbist_req_val_rdy_stable;
    @(posedge clk) disable iff (reset)
    lbist_req_val && !lbist_req_rdy |=> $stable(lbist_req_val) && $stable(lbist_req_msg);
  endproperty

  property lbist_req_msg_stable;
    @(posedge clk) disable iff (reset)
    lbist_req_val |-> $stable(lbist_req_msg);
  endproperty

  // LBIST Controller response interface
  property lbist_resp_val_rdy_stable;
    @(posedge clk) disable iff (reset)
    lbist_resp_val && !lbist_resp_rdy |=> $stable(lbist_resp_val) && $stable(lbist_resp_msg);
  endproperty

  property lbist_resp_msg_stable;
    @(posedge clk) disable iff (reset)
    lbist_resp_val |-> $stable(lbist_resp_msg);
  endproperty

  // No backpressure on response path when in DONE state
  property lbist_resp_rdy_in_done;
    @(posedge clk) disable iff (reset)
    (misr_inst.state == misr_inst.DONE) |-> lbist_resp_rdy;
  endproperty

  // Assertions
 // unique_hashes_assert:         assert property(unique_hashes);
  cut_val_rdy_handshake:        assert property(cut_val_rdy_stable);
  cut_msg_stable_assert:        assert property(cut_msg_stable);
  lbist_req_val_rdy_handshake:  assert property(lbist_req_val_rdy_stable);
  lbist_req_msg_stable_assert:  assert property(lbist_req_msg_stable);
  lbist_resp_val_rdy_handshake: assert property(lbist_resp_val_rdy_stable);
  lbist_resp_msg_stable_assert: assert property(lbist_resp_msg_stable);
  lbist_resp_rdy_done_assert:   assert property(lbist_resp_rdy_in_done);

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