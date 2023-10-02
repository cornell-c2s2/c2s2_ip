`default_nettype none
`include "src/serdes/deserializer.v"

module DeserializerHarness #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input logic [BIT_WIDTH - 1:0] recv_msg,
  input logic recv_val,
  output logic recv_rdy,

  output logic [BIT_WIDTH * N_SAMPLES - 1:0] send_msg,
  input logic send_rdy,
  output logic send_val,

  input logic reset,
  input logic clk
);

  logic [BIT_WIDTH - 1:0] send_msg_intermediate[N_SAMPLES - 1:0];

  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin : l_pack
      assign send_msg[BIT_WIDTH*i+:BIT_WIDTH] = send_msg_intermediate[i][BIT_WIDTH-1:0];
    end
  endgenerate

  Deserializer #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) deserializer (
    .recv_msg(recv_msg),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),

    .send_msg(send_msg_intermediate),
    .send_val(send_val),
    .send_rdy(send_rdy),

    .reset(reset),
    .clk  (clk)
  );
endmodule
