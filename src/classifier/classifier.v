//================================================
// classifier.v
//================================================
`default_nettype none
`ifndef CLASSIFIER_V
`define CLASSIFIER_V
`include "cmn/regs.v"
`include "classifier/helpers/magnitude.v"
`include "classifier/helpers/highpass.v"
`include "classifier/helpers/frequency_bins.v"
`include "classifier/helpers/comparison.v"

module classifier_Classifier #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  // bit width used for frequency calculations
  // this should be large enough to handle the sampling frequency
  parameter int FREQ_BIT_WIDTH = 16,
  parameter int N_SAMPLES = 8
) (
  input logic clk,
  input logic reset,

  output logic                   recv_rdy,
  input  logic                   recv_val,
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],

  output logic                        cutoff_freq_rdy,
  input  logic                        cutoff_freq_val,
  input  logic [FREQ_BIT_WIDTH - 1:0] cutoff_freq_msg,

  output logic                   cutoff_mag_rdy,
  input  logic                   cutoff_mag_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_mag_msg,

  output logic                        sampling_freq_rdy,
  input  logic                        sampling_freq_val,
  input  logic [FREQ_BIT_WIDTH - 1:0] sampling_freq_msg,

  input  logic send_rdy,
  output logic send_val,
  output logic send_msg
);

  logic [FREQ_BIT_WIDTH-1:0] in_cutoff_freq;
  logic [BIT_WIDTH-1:0] in_cutoff_mag;
  logic [FREQ_BIT_WIDTH-1:0] in_sampling_freq;

  cmn_EnResetReg #(
    .p_nbits      (FREQ_BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_freq_in (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_freq_msg),
    .q    (in_cutoff_freq),
    .en   (cutoff_freq_val)
  );
  assign cutoff_freq_rdy = 1;

  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_mag_in (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_mag_msg),
    .q    (in_cutoff_mag),
    .en   (cutoff_mag_val)
  );
  assign cutoff_mag_rdy = 1;

  cmn_EnResetReg #(
    .p_nbits      (FREQ_BIT_WIDTH),
    .p_reset_value(0)
  ) sampling_freq_in (
    .clk  (clk),
    .reset(reset),
    .d    (sampling_freq_msg),
    .q    (in_sampling_freq),
    .en   (sampling_freq_val)
  );
  assign sampling_freq_rdy = 1;

  // Calculate the magnitude combinational
  logic [BIT_WIDTH-1:0] out_mag[N_SAMPLES];

  magnitude_Magnitude #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) mag_calc (
    .recv_msg(recv_msg),
    .send_msg(out_mag)
  );

  // Filter based on cutoff
  logic [FREQ_BIT_WIDTH-1:0] frequency_array[N_SAMPLES];

  classifier_helpers_FrequencyBins #(
    .BIT_WIDTH(FREQ_BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) freq_gen (
    .sampling_freq(in_sampling_freq),
    .frequency_out(frequency_array)
  );

  logic out_filter[N_SAMPLES];

  highpass_Highpass #(
    .BIT_WIDTH(FREQ_BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) highpass_fil (
    .cutoff_freq(in_cutoff_freq),
    .freq_in(frequency_array),
    .filtered_valid(out_filter)
  );

  // Do comparison mag > cutoff_mag
  logic out_comparison;

  comparison_Comparison #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) comparison (
    .cutoff_mag(in_cutoff_mag),
    .filtered_valid(out_filter),
    .mag_in(out_mag),
    .compare_out(out_comparison)
  );

  assign send_msg = out_comparison;
  assign send_val = recv_val;
  assign recv_rdy = send_rdy;
endmodule

`endif