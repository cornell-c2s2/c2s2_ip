
`include "src/fft/pease/fft.v"
`include "src/serdes/deserializer.v"
`include "src/serdes/serializer.v"

module FFTHarness #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg,
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic                   send_val,
  input  logic                   send_rdy,

  input logic reset,
  input logic clk
);

  logic recv_val_t;
  logic recv_rdy_t;
  logic [BIT_WIDTH - 1:0] recv_msg_t[N_SAMPLES - 1:0];
  logic send_val_t;
  logic send_rdy_t;
  logic [BIT_WIDTH - 1:0] send_msg_t[N_SAMPLES - 1:0];

  serdes_Deserializer #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) deser (
    .recv_msg(recv_msg),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),

    .send_msg(recv_msg_t),
    .send_val(recv_val_t),
    .send_rdy(recv_rdy_t),

    .reset(reset),
    .clk  (clk)
  );

  serdes_Serializer #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) ser (
    .recv_msg(send_msg_t),
    .recv_val(send_val_t),
    .recv_rdy(send_rdy_t),

    .send_msg(send_msg),
    .send_val(send_val),
    .send_rdy(send_rdy),

    .reset(reset),
    .clk  (clk)
  );

  FFT #(
    .BIT_WIDTH (BIT_WIDTH),
    .DECIMAL_PT(DECIMAL_PT),
    .N_SAMPLES (N_SAMPLES)
  ) comb_fft (
    .recv_msg(recv_msg_t),
    .recv_val(recv_val_t),
    .recv_rdy(recv_rdy_t),

    .send_msg(send_msg_t),
    .send_val(send_val_t),
    .send_rdy(send_rdy_t),

    .reset(reset),
    .clk  (clk)
  );

endmodule
