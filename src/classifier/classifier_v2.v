`include "cmn/regs.v"
`include "classifier/helpers/sum.v"
`include "cmn/counters.v"
`include "classifier/helpers/classifier_regs.v"

module classifier_Classifier #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 32
) (
  input logic clk,
  input logic reset,

  output logic                   recv_rdy,
  input  logic                   recv_val,
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES - 1:0],

  output logic                   cutoff_idx_low_rdy,
  input  logic                   cutoff_idx_low_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_idx_low_msg,

  output logic                   cutoff_idx_high_rdy,
  input  logic                   cutoff_idx_high_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_idx_high_msg,

  output logic                   cutoff_mag_rdy,
  input  logic                   cutoff_mag_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_mag_msg,

  input  logic send_rdy,
  output logic send_val,
  output logic send_msg

);

  logic [BIT_WIDTH-1:0] magnitude [N_SAMPLES-1:0];

  arr_EnResetReg #(
    .BIT_WIDTH  (BIT_WIDTH),
    .RESET_VALUE({BIT_WIDTH{1'b0}}),
    .N_ELEMENTS (N_SAMPLES)
  ) classifier_in (
    .clk  (clk),
    .reset(reset),
    .d    (recv_msg),
    .q    (magnitude),
    .en   (recv_val)
  );
  assign recv_rdy = 1;

  // we use id in the sample rather than frequency
  // to avoid extra calculations
  logic [BIT_WIDTH - 1 : 0] cutoff_idx_low;
  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_freq_low_reg (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_idx_low_msg),
    .q    (cutoff_idx_low),
    .en   (cutoff_idx_low_val)
  );
  assign cutoff_idx_low_rdy = 1;

  logic [BIT_WIDTH - 1 : 0] cutoff_idx_high;
  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_freq_high_reg (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_idx_high_msg),
    .q    (cutoff_idx_high),
    .en   (cutoff_idx_high_val)
  );
  assign cutoff_idx_high_rdy = 1;

  // store threshold
  logic [BIT_WIDTH - 1 : 0] cutoff_mag;
  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_mag_reg (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_mag_msg),
    .q    (cutoff_mag),
    .en   (cutoff_mag_val)
  );
  assign cutoff_mag_rdy = 1;

  // Lower half convolution
  logic [BIT_WIDTH-1:0] convLowHalf;
  classifier_helpers_Sum #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES / 2)
  ) sumLowHalf (
    .clk  (clk),
    .reset(reset),
    .arr  (magnitude[N_SAMPLES/2-1:0]),
    .sum  (convLowHalf)
  );

  // Upper half convolution
  logic [BIT_WIDTH-1:0] convHighHalf;
  classifier_helpers_Sum #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES / 2)
  ) sumHighHalf (
    .clk  (clk),
    .reset(reset),
    .arr  (magnitude[N_SAMPLES-1:N_SAMPLES/2]),
    .sum  (convHighHalf)
  );

  // Maximum magnitude of the input array
  // the nth element of max_mag is the maximum magnitude of the first n elements of the input array
  logic [BIT_WIDTH-1:0] max_mags[N_SAMPLES-1:0];

  generate
    assign max_mags[0] = magnitude[0];
    for (genvar i = 1; i < N_SAMPLES; i++) begin
      // if we are below cutoff low or above cutoff high, we don't care about the magnitude
      // so we set it to 0
      logic [BIT_WIDTH-1:0] mag;
      assign mag = (i < cutoff_idx_low || i > cutoff_idx_high) ? 0 : magnitude[i];
      assign max_mags[i] = max_mags[i-1] > mag ? max_mags[i-1] : mag;
    end
  endgenerate

  // is max magnitude above threshold?
  logic mag_detected;
  assign mag_detected = max_mags[N_SAMPLES-1] > cutoff_mag;

  // incrementers for on_cycle and off_cycle
  logic on_cycle_count_is_max;
  cmn_BasicCounter #(
    .p_count_nbits      (16),
    .p_count_clear_value(0),
    .p_count_max_value  (300)  // TODO: Make this configurable
  ) on_cycle_counter (
    .clk          (clk),
    .reset        (reset),
    .clear        (!mag_detected),
    .increment    (mag_detected),          // increment on cycle if magnitude is above threshold
    .decrement    (1'b0),
    .count        (),
    .count_is_zero(),
    .count_is_max (on_cycle_count_is_max)
  );


  logic off_cycle_count_is_max;
  cmn_BasicCounter #(
    .p_count_nbits      (16),
    .p_count_clear_value(0),
    .p_count_max_value  (2000)  // TODO: Make this configurable
  ) off_cycle_counter (
    .clk          (clk),
    .reset        (reset),
    .clear        (mag_detected),
    .increment    (!mag_detected),
    .decrement    (1'b0),                   // decrement off cycle if magnitude is above threshold
    .count        (),
    .count_is_zero(),
    .count_is_max (off_cycle_count_is_max)
  );

  logic has_sound;

  always_ff @(posedge clk) begin
    if (reset) begin
      has_sound <= 1'b0;
    end else begin
      if (on_cycle_count_is_max) begin
        // if on_cycle > 300, start recording sound
        has_sound <= 1'b1;
      end else if (off_cycle_count_is_max) begin
        // if off_cycle > 2000, stop recording sound
        has_sound <= 1'b0;
      end else begin
        has_sound <= has_sound;
      end
    end
  end

  // pass through sound
  logic curr_sound;
  assign curr_sound = (has_sound || on_cycle_count_is_max) && !off_cycle_count_is_max;

  // count decrementer
  logic count_is_zero;
  cmn_BasicCounter #(
    .p_count_nbits      (16),
    .p_count_clear_value(9),   // TODO: Make this configurable
    .p_count_max_value  (10)   // TODO: Make this configurable
  ) count_decrementer (
    .clk          (clk),
    .reset        (reset),
    .clear        (has_sound),      // set to 10 if has_sound
    .increment    (1'b0),
    .decrement    (1'b1),           // always decrement
    .count        (),
    .count_is_zero(count_is_zero),
    .count_is_max ()
  );

  // TODO: Handle val/rdy stuff
  assign send_msg = curr_sound || !count_is_zero;
  assign send_val = recv_val;


endmodule
