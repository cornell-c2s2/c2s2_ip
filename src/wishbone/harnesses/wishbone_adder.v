`default_nettype none
`include "src/wishbone/adder.v"
`include "src/wishbone/wishbone.v"
`include "src/cmn/trace.v"

module WishboneAdderHarness (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [69:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [32:0] send_msg
);
  assign recv_rdy = 1;
  assign send_val = 1;
  // proc -> wb
  // recv_msg
  //     69          68        67       66:64      63:32     31:0
  // +----------+---------+---------+---------+----------+-----------+
  // wbs_stb_i  wbs_cyc_i  wbs_we_i  wbs_sel_i  wbs_dat_i  wbs_adr_i

  // wb -> proc
  // resp_msg
  //    32         31:0
  // +----------+---------+
  //  wbs_ack_o  wbs_dat_o

  // adder -> wb
  logic c_i_stream_rdy;
  logic [31:0] c_o_stream_data;
  logic c_o_stream_val;

  // wb -> adder
  logic c_i_stream_val;
  logic [31:0] c_i_stream_data;
  logic c_o_stream_rdy;

  Wishbone #(1) wb (
    //inputs
    .clk  (clk),
    .reset(reset),

    //proc ->  wb
    .wbs_stb_i(recv_msg[69]),
    .wbs_cyc_i(recv_msg[68]),
    .wbs_we_i (recv_msg[67]),
    .wbs_sel_i(recv_msg[66:64]),
    .wbs_dat_i(recv_msg[63:32]),
    .wbs_adr_i(recv_msg[31:0]),

    //wb -> proc
    .wbs_ack_o(send_msg[32]),
    .wbs_dat_o(send_msg[31:0]),

    //wb -> adder
    .i_stream_val (c_i_stream_val),
    .i_stream_data(c_i_stream_data),
    .o_stream_rdy (c_o_stream_rdy),

    //adder -> wb
    .i_stream_rdy (c_i_stream_rdy),
    .o_stream_val (c_o_stream_val),
    .o_stream_data(c_o_stream_data)

  );

  Adder adder (
    .clk  (clk),
    .reset(reset),

    // inputs
    .i_stream_val (c_i_stream_val),
    .i_stream_data(c_i_stream_data),
    .o_stream_rdy (c_o_stream_rdy),

    // outputs
    .i_stream_rdy (c_i_stream_rdy),
    .o_stream_val (c_o_stream_val),
    .o_stream_data(c_o_stream_data)
  );

`ifndef SYNTHESIS

  logic [32-1:0] str;
  `CMN_TRACE_BEGIN
  begin

    $sformat(str, "%x", c_i_stream_data);
    cmn_trace.append_val_rdy_str(
        trace_str, c_i_stream_val, c_i_stream_rdy, str
    ); cmn_trace.append_str(
        trace_str, "("
    );
  end
  `CMN_TRACE_END
`endif  /* SYNTHESIS */


endmodule
