//========================================================================
// Verilog Components: Test Source with Random Delays
//========================================================================

`ifndef VC_TEST_RAND_DELAY_SOURCE_V
`define VC_TEST_RAND_DELAY_SOURCE_V

`include "vc/TestSource.v"
`include "vc/TestRandDelay.v"

module vc_TestRandDelaySource
#(
  parameter p_msg_nbits = 1,
  parameter p_num_msgs  = 1024
)(
  input  logic                   clk,
  input  logic                   reset,

  // Max delay input

  input  logic [31:0]            max_delay,

  // Source message interface

  output logic                   val,
  input  logic                   rdy,
  output logic [p_msg_nbits-1:0] msg,

  // Goes high once all source data has been issued

  output logic                   done
);

  //----------------------------------------------------------------------
  // Test source
  //----------------------------------------------------------------------

  logic                   src_val;
  logic                   src_rdy;
  logic [p_msg_nbits-1:0] src_msg;

  vc_TestSource#(p_msg_nbits,p_num_msgs) src
  (
    .clk       (clk),
    .reset     (reset),

    .val       (src_val),
    .rdy       (src_rdy),
    .msg       (src_msg),

    .done      (done)
  );

  //----------------------------------------------------------------------
  // Test random delay
  //----------------------------------------------------------------------

  vc_TestRandDelay#(p_msg_nbits) msg_delay
  (
    .clk       (clk),
    .reset     (reset),

    .max_delay (max_delay),

    .in_val    (src_val),
    .in_rdy    (src_rdy),
    .in_msg    (src_msg),

    .out_val   (val),
    .out_rdy   (rdy),
    .out_msg   (msg)
  );

endmodule

`endif /* VC_TEST_RAND_DELAY_SOURCE */
