`include "fft/helpers/sine_wave.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"
`include "fft/helpers/fft_stage.v"

module FFTStageHarness #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8,
  parameter int STAGE_FFT  = 0
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

  logic [BIT_WIDTH - 1:0] sine_wave_out[0:N_SAMPLES - 1];

  SineWave #(
    .N(N_SAMPLES),
    .W(BIT_WIDTH),
    .D(DECIMAL_PT)
  ) sine_wave (
    .sine_wave_out(sine_wave_out)
  );

  logic recv_val_t;
  logic recv_rdy_t;
  logic [BIT_WIDTH - 1:0] recv_msg_t[2*N_SAMPLES - 1:0];
  logic send_val_t;
  logic send_rdy_t;
  logic [BIT_WIDTH - 1:0] send_msg_t[2*N_SAMPLES - 1:0];

  Deserializer #(
    .N_SAMPLES(2 * N_SAMPLES),
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

  Serializer #(
    .N_SAMPLES(2 * N_SAMPLES),
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


  FFTStage #(
    .BIT_WIDTH (BIT_WIDTH),
    .DECIMAL_PT(DECIMAL_PT),
    .N_SAMPLES (N_SAMPLES),
    .STAGE_FFT (STAGE_FFT)
  ) fft_stage (
    .recv_msg_real(recv_msg_t[N_SAMPLES-1:0]),
    .recv_msg_imag(recv_msg_t[2*N_SAMPLES-1:N_SAMPLES]),
    .recv_val     (recv_val_t),
    .recv_rdy     (recv_rdy_t),

    .send_msg_real(send_msg_t[N_SAMPLES-1:0]),
    .send_msg_imag(send_msg_t[2*N_SAMPLES-1:N_SAMPLES]),
    .send_val     (send_val_t),
    .send_rdy     (send_rdy_t),

    .sine_wave_out(sine_wave_out),

    .reset(reset),
    .clk  (clk)
  );

endmodule
