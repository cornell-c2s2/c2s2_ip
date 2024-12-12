`include "spi/minion.v"

module spi_Minion_sva #(
    parameter BIT_WIDTH = 32,
    parameter N_SAMPLES = 8
) (
    input  logic                   clk,
    input  logic                   reset,
    input  logic                   cs,
    input  logic                   sclk,
    input  logic                   mosi,
    output logic                   miso,
    input  logic [BIT_WIDTH - 1:0] recv_msg,
    output logic                   recv_rdy,
    input  logic                   recv_val,
    output logic [BIT_WIDTH - 1:0] send_msg,
    input  logic                   send_rdy,
    output logic                   send_val,
    output logic                   minion_parity,
    output logic                   adapter_parity
);

  // Local parameters for parity calculation
  localparam PARITY_WIDTH = BIT_WIDTH - 3;
  
  // Helper function for parity calculation
  function automatic logic calc_parity;
    input logic [BIT_WIDTH-1:0] data;
    input logic valid;
    logic result;
    result = 0;
    for (int i = 0; i < PARITY_WIDTH; i++) begin
      result ^= data[i];
    end
    return result & valid;
  endfunction

  // Property and sequence definitions
  // Verify byte-aligned message size
  property BYTE_ALIGNED_SIZE_PROP;
    (BIT_WIDTH % 8) == 0;
  endproperty

  // Verify that chip select remains stable (low) for the duration of a transfer
  property CS_STABLE_PROP;
    $fell(cs) |-> ##[1:BIT_WIDTH] !$rose(cs);
  endproperty

  // Ensure that sent data is never unknown when valid
  property DATA_VALID_PROP;
    (send_val && send_rdy) |-> !$isunknown(send_msg);
  endproperty

  // Verify that parity bits from minion and adapter modules match
  property PARITY_MATCH_PROP;
    send_val |-> (minion_parity == adapter_parity);
  endproperty

  // Updated parity check to match specification
  property PARITY_CALC_PROP;
    send_val |-> (minion_parity == (^send_msg[PARITY_WIDTH-1:0] & send_val));
  endproperty

  // Define sequence for a complete SPI transfer
  sequence TRANSFER_COMPLETE_SEQ;
    $fell(cs) ##[1:BIT_WIDTH] $rose(cs);
  endsequence

  // Define sequence for message end (CS rising edge)
  sequence MSG_END_SEQ;
    $rose(cs);
  endsequence

  // Define sequence for message start (CS falling edge)
  sequence MSG_START_SEQ;
    $fell(cs);
  endsequence

  // Verify minimum 4-cycle spacing between messages
  property MSG_SPACING_PROP;
    MSG_END_SEQ |=> ##[4:$] MSG_START_SEQ;
  endproperty

  // Assertions
  // Verify CS stability during transfers
  CS_STABLE_CHK:    assert property(@(posedge clk) CS_STABLE_PROP);
  // Verify data validity when being sent
  DATA_VALID_CHK:   assert property(@(posedge clk) DATA_VALID_PROP);
  // Verify parity consistency between modules
  PARITY_CHK:       assert property(@(posedge clk) PARITY_MATCH_PROP);
  // Verify message spacing requirement
  MSG_SPACING_CHK:  assert property(@(posedge clk) MSG_SPACING_PROP);
  // Verify byte-aligned message size
  BYTE_ALIGNED_CHK:  assert property(BYTE_ALIGNED_SIZE_PROP)
    else $error("Message size must be byte-aligned");
  // Verify parity calculation
  PARITY_CALC_CHK:   assert property(@(posedge clk) PARITY_CALC_PROP);

  // Coverage points
  // Coverage for complete SPI transfers
  TRANSFER_CVR:    cover property(@(posedge clk) TRANSFER_COMPLETE_SEQ);
  // Coverage for successful send operations
  SEND_CVR:        cover property(@(posedge clk) send_val && send_rdy);
  // Coverage for successful receive operations
  RECV_CVR:        cover property(@(posedge clk) recv_val && recv_rdy);
  // Coverage for minimum message spacing
  MSG_SPACING_CVR: cover property(@(posedge clk) MSG_END_SEQ ##4 MSG_START_SEQ);
  // Additional coverage points
  PARITY_ONE_CVR:    cover property(@(posedge clk) minion_parity == 1'b1);
  PARITY_ZERO_CVR:   cover property(@(posedge clk) minion_parity == 1'b0);
  MSB_CONTROL_CVR:   cover property(@(posedge clk) send_val &&
                      (|send_msg[BIT_WIDTH-1:BIT_WIDTH-2]));

endmodule

bind spi_Minion spi_Minion_sva tb(.*);
