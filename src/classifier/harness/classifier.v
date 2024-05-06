`default_nettype none
`include "classifier/classifier_v2.v"

module classifier_HarnessClassifier #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [N_SAMPLES*BIT_WIDTH-1:0] recv_msg,

  output logic                   cutoff_idx_low_rdy,
  input  logic                   cutoff_idx_low_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_idx_low_msg,

  output logic                   cutoff_idx_high_rdy,
  input  logic                   cutoff_idx_high_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_idx_high_msg,

  output logic                   cutoff_mag_rdy,
  input  logic                   cutoff_mag_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_mag_msg,

  output logic send_val,
  input  logic send_rdy,
  output logic send_msg
);

  logic [BIT_WIDTH-1:0] imm_recv_msg[N_SAMPLES-1:0];

  classifier_Classifier #(BIT_WIDTH, N_SAMPLES) Classifier (
    .clk  (clk),
    .reset(reset),

    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .recv_msg(imm_recv_msg),

    .cutoff_idx_low_rdy(cutoff_idx_low_rdy),
    .cutoff_idx_low_val(cutoff_idx_low_val),
    .cutoff_idx_low_msg(cutoff_idx_low_msg),
    .cutoff_idx_high_rdy(cutoff_idx_high_rdy),
    .cutoff_idx_high_val(cutoff_idx_high_val),
    .cutoff_idx_high_msg(cutoff_idx_high_msg),
    .cutoff_mag_rdy(cutoff_mag_rdy),
    .cutoff_mag_val(cutoff_mag_val),
    .cutoff_mag_msg(cutoff_mag_msg),

    .send_val(send_val),
    .send_rdy(send_rdy),
    .send_msg(send_msg)
  );

  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin : output_gen
      assign imm_recv_msg[i] = recv_msg[(i+1)*BIT_WIDTH-1:i*BIT_WIDTH];
    end
  endgenerate

endmodule
