`include "src/lbist/misr/misr.v" 

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

// add all outputted hashes to a register
logic [SIGNATURE_BITS-1:0] hashes[MAX_OUTPUTS_TO_HASH-1:0];
always_ff @(posedge clk) begin
  if (reset) begin
    hashes <= '0;
  end else if (lbist_resp_val && lbist_resp_rdy) begin
      hashes[lbist_req_msg] <= lbist_resp_msg;
  end
end

// validate that all the hashes generated are unique
property unique_hashes;
  @(posedge clk)
  disable iff (!reset)
  (lbist_resp_val && lbist_resp_rdy) |-> 

endmodule
 
bind misr_sva misr misr_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .data_out(data_out)
);