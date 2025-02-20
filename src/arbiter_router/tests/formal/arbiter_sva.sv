`include "arbiter_router/arbiter.v"

module arbiter_sva #(
  parameter int nbits   = 32,
  parameter int ninputs = 3,
  localparam int addr_nbits = $clog2(ninputs)
)(
  input  logic clk,
  input  logic reset,
  
  // Input (receive) interface for each source.
  input logic             istream_val [ninputs],
  input logic             istream_rdy [ninputs],
  input logic [nbits-1:0] istream_msg [ninputs],
  
  // Output (send) interface.
  input logic                        ostream_val,
  input logic                        ostream_rdy,
  input logic [addr_nbits+nbits-1:0] ostream_msg
);

  //-------------------------------------------------------------------------
  // Assertion 1: Output Message Consistency
  // The output message should be the concatenation of the current grant (address)
  // and the message of that input.
  //-------------------------------------------------------------------------
  property p_output_message;
    @(posedge clk) disable iff (reset)
      ostream_msg === {grants_index, istream_msg[grants_index]};
  endproperty

  assert property (p_output_message)

  //-------------------------------------------------------------------------
  // Assertion 2: Output Valid Handshake Consistency
  // The arbiter’s output valid signal is defined as:
  //    ostream_val = istream_val[grants_index] & ostream_rdy
  //-------------------------------------------------------------------------
  property p_output_valid;
    @(posedge clk) disable iff (reset)
      ostream_val === (istream_val[grants_index] & ostream_rdy);
  endproperty

  assert property (p_output_valid)

  //-------------------------------------------------------------------------
  // Assertion 3: Only the Granted Input Receives a Ready Signal
  // Each input’s ready signal is driven as follows:
  //    if (i == grants_index) then istream_rdy[i] = ostream_rdy,
  //    else                     istream_rdy[i] = 0.
  //-------------------------------------------------------------------------
  genvar i;
  generate
    for (i = 0; i < ninputs; i = i+1) begin : check_ready
      property p_only_granted_ready;
        @(posedge clk) disable iff (reset)
          (grants_index == i) ? (istream_rdy[i] === ostream_rdy)
                              : (istream_rdy[i] === 1'b0);
      endproperty

      assert property (p_only_granted_ready)
        else $error("Arbiter: Input %0d received an incorrect ready signal.", i);
    end
  endgenerate

  //-------------------------------------------------------------------------
  // Assertion 4: Hold Behavior
  // If the previously granted input (old_grants_index) is still valid,
  // then the current grant must remain the same.
  //-------------------------------------------------------------------------
  property p_hold_previous;
    @(posedge clk) disable iff (reset)
      (istream_val[old_grants_index] == 1'b1)
        |-> (grants_index === old_grants_index);
  endproperty

  assert property (p_hold_previous)
    else $error("Arbiter: Grant not held when the previous input remains valid.");

  //-------------------------------------------------------------------------
  // Assertion 5: Update Behavior
  // When the previously granted input becomes invalid,
  // the arbiter must update the grant to match the output of the priority encoder.
  //-------------------------------------------------------------------------
  property p_update_grant;
    @(posedge clk) disable iff (reset)
      (istream_val[old_grants_index] == 1'b0)
        |-> (grants_index === encoder_out);
  endproperty

  assert property (p_update_grant)
    else $error("Arbiter: Grant did not update correctly when previous input became invalid.");

endmodule
