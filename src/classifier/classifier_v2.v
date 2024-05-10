`include "cmn/regs.v"
`include "classifier/helpers/sum.v"
`include "cmn/counters.v"
`include "classifier/helpers/classifier_regs.v"

module classifier_Classifier #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
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

  /////////////////////////////////////////////////////////////////////////////
  // Input registers
  /////////////////////////////////////////////////////////////////////////////

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

  /////////////////////////////////////////////////////////////////////////////
  // Convolutions
  /////////////////////////////////////////////////////////////////////////////

  // Vertical convolution
  logic [BIT_WIDTH-1:0] convVert;
  classifier_helpers_Sum #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) sumVert (
    .clk  (clk),
    .reset(reset),
    .arr  (magnitude[N_SAMPLES-1:0]),
    .sum  (convVert)
  );

  // Lower half convolution
  logic [BIT_WIDTH-1:0] convLowHalf_tmp;
  classifier_helpers_Sum #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES / 2)
  ) sumLowHalf (
    .clk  (clk),
    .reset(reset),
    .arr  (magnitude[N_SAMPLES/2-1:0]),
    .sum  (convLowHalf_tmp)
  );
  // multiply by two (like in python model)
  logic [BIT_WIDTH-1:0] convLowHalf;
  assign convLowHalf = convLowHalf_tmp << 1;

  // Upper half convolution
  logic [BIT_WIDTH-1:0] convHighHalf_tmp;
  classifier_helpers_Sum #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES / 2)
  ) sumHighHalf (
    .clk  (clk),
    .reset(reset),
    .arr  (magnitude[N_SAMPLES-1:N_SAMPLES/2]),
    .sum  (convHighHalf_tmp)
  );
  // multiply by two (like in python model)
  logic [BIT_WIDTH-1:0] convHighHalf;
  assign convHighHalf = convHighHalf_tmp << 1;

  /////////////////////////////////////////////////////////////////////////////
  // Find Maximum Magnitude
  /////////////////////////////////////////////////////////////////////////////

  // Maximum magnitude of the input array
  logic [BIT_WIDTH-1:0] max_mag;

  always @(posedge clk) begin 
    if (reset) begin
      max_mag <= 0;
    end
    else begin
      for (integer i = 0; i < N_SAMPLES; i = i + 1) begin
        if (magnitude[i] > cutoff_mag) begin
          if (i < cutoff_idx_low || i > cutoff_idx_high) begin // reduce magnitude outside interval
            if (magnitude[i] > max_mag) begin
              max_mag <= magnitude[i] >> 3; // Reduce magnitude by factor of 0.125
            end
          end
          else begin
            if (magnitude[i] > max_mag) begin // amplify magnitude within interval
              max_mag <= magnitude[i] << 4; // Increase magnitude by factor of 16
            end
          end
        end
      end
    end
  end

  // generate
  //   for (genvar i = 1; i < N_SAMPLES; i++) begin
  //     // if we are below cutoff low or above cutoff high, we don't care about the magnitude
  //     // so we set it to a small number
  //     if (magnitude[i] > cutoff_mag) begin
  //       if ((i < cutoff_idx_low || i > cutoff_idx_high) && (magnitude[i] > max_mag)) begin
  //         assign max_mag = magnitude[i] >> 3; // mag * 0.125
  //       end
  //       else begin
  //         assign max_mag = magnitude[i] << 4; // mag * 16
  //       end
  //     end
  //     else begin
  //       assign max_mag = max_mag;
  //     end
  //   end
  // endgenerate


  // // Maximum magnitude of the input array
  // // the nth element of max_mag is the maximum magnitude of the first n elements of the input array
  // logic [BIT_WIDTH-1:0] max_mags[N_SAMPLES-1:0];

  // generate
  //   assign max_mags[0] = magnitude[0];
  //   for (genvar i = 1; i < N_SAMPLES; i++) begin
  //     // if we are below cutoff low or above cutoff high, we don't care about the magnitude
  //     // so we set it to 0
  //     logic [BIT_WIDTH-1:0] mag;
  //     assign mag = (i < cutoff_idx_low || i > cutoff_idx_high) ? 0 : magnitude[i];
  //     assign max_mags[i] = max_mags[i-1] > mag ? max_mags[i-1] : mag;
  //   end
  // endgenerate

  // assign max_mag = max_mags[N_SAMPLES-1];

  /////////////////////////////////////////////////////////////////////////////
  // ON_CYCLE and OFF_CYCLE Counters
  /////////////////////////////////////////////////////////////////////////////

  // TODO: make this configurable (it's 0.5 by putting a 1 in the DECIMAL MSB)
  logic max_mag_above_point_five;
  assign max_mag_above_point_five = max_mag > (1 << (DECIMAL_PT-1)); 

  // TODO: make this configurable (it's 0.25 by putting a 1 in the DECIMAL MSB)
  logic max_mag_below_point_three;
  assign max_mag_below_point_three = max_mag < (1 << (DECIMAL_PT-2)); 

  // incrementers for on_cycle and off_cycle
  logic on_cycle_count_is_max;
  cmn_BasicCounter #(
    .p_count_nbits      (16),
    .p_count_clear_value(0),
    .p_count_max_value  (300)  // TODO: Make this configurable
  ) on_cycle_counter (
    .clk          (clk),
    .reset        (reset),
    .clear        (max_mag_below_point_three),
    .increment    (max_mag_above_point_five),          // increment on cycle if magnitude is above threshold
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
    .clear        (max_mag_above_point_five),
    .increment    (max_mag_below_point_three),
    .decrement    (1'b0),                   // decrement off cycle if magnitude is above threshold
    .count        (),
    .count_is_zero(),
    .count_is_max (off_cycle_count_is_max)
  );

  /////////////////////////////////////////////////////////////////////////////
  // CURR_SOUND Logic
  /////////////////////////////////////////////////////////////////////////////

  // pass through sound
  logic curr_sound;
  always_ff @(posedge clk) begin
    if (reset) begin
      curr_sound <= 1'b0;
    end else begin
      if (on_cycle_count_is_max) begin
        // if on_cycle > 300, start recording sound
        curr_sound <= 1'b1;
      end else if (off_cycle_count_is_max) begin
        // if off_cycle > 2000, stop recording sound
        curr_sound <= 1'b0;
      end else begin
        curr_sound <= curr_sound;
      end
    end
  end

  // // count decrementer
  // logic count_is_zero;
  // cmn_BasicCounter #(
  //   .p_count_nbits      (16),
  //   .p_count_clear_value(9),   // TODO: Make this configurable
  //   .p_count_max_value  (10)   // TODO: Make this configurable
  // ) count_decrementer (
  //   .clk          (clk),
  //   .reset        (reset),
  //   .clear        (curr_sound && (convLowHalf > convVert)),      // set to 10 if has_sound
  //   .increment    (1'b0),
  //   .decrement    (!count_is_zero),           // decrement when count is greater than 0
  //   .count        (),
  //   .count_is_zero(count_is_zero),
  //   .count_is_max ()
  // );

  /////////////////////////////////////////////////////////////////////////////
  // Count Decrementer
  /////////////////////////////////////////////////////////////////////////////
  logic [BIT_WIDTH-1:0] count;

  always_ff @(posedge clk) begin
    if (reset) begin
      count <= 0;
    end
    else if (curr_sound && (convLowHalf > convVert)) begin
      count <= 9;
    end
    else begin
      count <= 0;
    end

    if (count > 0) begin
      count <= count - 1;
    end
  end

  // TODO: Handle val/rdy stuff
  assign send_msg = (count > 0);
  assign send_val = recv_val;


endmodule
