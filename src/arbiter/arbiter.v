// ==========================================================================
// Arbitrator module
// ==========================================================================
// This module is used to pick which component gets to output to the val/rdy
// SPI wrapper if multiple components can send a valid message.
// The arbitrator puts an address header on the outgoing packet so that
// downstream components can tell which component sent the response
// The nbits parameter is the length of the message.
// The num_inputs parameter is the number of input components that the Arbitrator is selecting from.
// NOTE: MUST be >= 2

// Original   : Dilan Lakhani
// Date       : Dec 19, 2021

module Arbiter #(
  parameter nbits = 32,
  parameter ninputs = 3,
  parameter addr_nbits = $clog2(ninputs)
) (
  input logic clk,
  input logic reset,

  // Receive Interface - need recv signals for each component connected to arbitrator
  input  logic             istream_val[0:ninputs-1],
  output logic             istream_rdy[0:ninputs-1],
  input  logic [nbits-1:0] istream_msg[0:ninputs-1],

  // Send Interface
  output logic                        ostream_val,
  input  logic                        ostream_rdy,
  output logic [addr_nbits+nbits-1:0] ostream_msg
);
  logic [addr_nbits-1:0] grants_index;  // which input is granted access to send to SPI
  logic [addr_nbits-1:0] old_grants_index;
  logic [addr_nbits-1:0] encoder_out;
  logic [     nbits-1:0] ostream_msg_data;
  logic [addr_nbits-1:0] ostream_msg_addr;

  assign ostream_msg_data = istream_msg[grants_index];
  assign ostream_msg_addr = grants_index;
  assign ostream_val = istream_val[grants_index] & istream_rdy[grants_index];
  assign ostream_msg = {
    ostream_msg_addr, ostream_msg_data
  };  // append component address to the beginning of the message  


  always_comb begin
    // change grants_index if the last cycle's grant index is 0 (that component has finished sending its message)
    if (!istream_val[old_grants_index]) begin
      grants_index = encoder_out;
    end else begin
      grants_index = old_grants_index;
    end
  end

  always_comb begin
    for (integer j = 0; j < ninputs; j++) begin
      // Only tell one input that the arbitrator is ready for it
      if (grants_index == j) begin
        istream_rdy[j] = ostream_rdy;
      end else begin
        istream_rdy[j] = 1'b0;
      end
    end
  end

  always_comb begin
    // priority encoder that gives highest priority to the LSB and lowest to MSB
    encoder_out = 0;
    for (integer i = 0; i < ninputs; i++) begin
      if (istream_val[ninputs-1-i]) begin
        encoder_out = ninputs - 1 - i;
      end
    end
  end

  // One issue arises with having multiple Disassemblers. Since the SPI width is normally less than the size of a response,
  // a PacketDisassembler component needs multiple cycles to fully send a message to the arbitrator. Thus, we do not want to 
  // change which Disassembler is allowed to send to the Arbitrator in the middle of a message.
  // Fix this by holding a trailing value of the grants_index.
  // We need to be able to check the req_val of the old grants_index to make sure that it is not 1, then we can allow a different
  // Disassembler to send a message
  always_ff @(posedge clk) begin
    if (reset) begin
      old_grants_index <= 0;
    end else begin
      old_grants_index <= grants_index;
    end
  end

endmodule
