`default_nettype none
`include "serdes/serializer.v"
`include "serdes/deserializer.v"

module ConnectHarness #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  // serializer inputs & outputs
  input logic [BIT_WIDTH - 1:0] recv_msg,
  input logic recv_val,
  output logic recv_rdy,

  output logic send_val,
  input logic send_rdy,
  output logic [BIT_WIDTH - 1:0] send_msg,

  // clk and reset signals
  input logic reset,
  input logic clk
);
  // send to serializer
  logic d_rdy;
  logic d_val;
  logic [BIT_WIDTH - 1:0] d_msg[N_SAMPLES - 1:0];

  Deserializer #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) deserializer (
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .recv_msg(recv_msg),
    .send_val(d_val),
    .send_rdy(d_rdy),
    .send_msg(d_msg),
    .clk(clk),
    .reset(reset)
  );

  Serializer #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) serializer (
    .recv_val(d_val),  // output of deserializer
    .recv_rdy(d_rdy),  // serializer ready to recieve
    .recv_msg(d_msg),  // output of deserializer
    .send_val(send_val),
    .send_rdy(send_rdy),
    .send_msg(send_msg),
    .clk(clk),
    .reset(reset)
  );
endmodule
