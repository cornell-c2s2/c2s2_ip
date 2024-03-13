`default_nettype none
`include "classifier/classifier.v"

module classifier_HarnessClassifier #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES = 8,
  parameter int CUTOFF_FREQ = 65536000,  // 1000 in 16.16 : 1000*2^16
  parameter int CUTOFF_MAG = 1310720,  // 20 in 16.16 : 20*2^16
  parameter int SAMPLING_FREQUENCY = 44000
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [N_SAMPLES*BIT_WIDTH-1:0] recv_msg,

  output logic send_val,
  input  logic send_rdy,
  output logic send_msg
);

  logic [BIT_WIDTH-1:0] imm_recv_msg[N_SAMPLES-1:0];

  classifier_Classifier #(BIT_WIDTH, DECIMAL_PT, N_SAMPLES, CUTOFF_FREQ, CUTOFF_MAG, SAMPLING_FREQUENCY) Classifier (
    .clk  (clk),
    .reset(reset),

    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .recv_msg(imm_recv_msg),

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
