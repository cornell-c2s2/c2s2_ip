//================================================
// classifier.v
//================================================
`default_nettype none
`ifndef CLASSIFIER_V
`define CLASSIFIER_V
`include "cmn/regs.v"
`include "classifier/helpers/magnitude.v"
`include "classifier/helpers/highpass.v"

module classifier_Classifier #(
  parameter int BIT_WIDTH   = 32,
  parameter int DECIMAL_PT  = 16,
  parameter int N_SAMPLES   = 8,
  parameter int CUTOFF_FREQ = 65536000,  // 1000 in 16.16 : 1000*2^16
  parameter int CUTOFF_MAG  = 1310720,   // 20 in 16.16 : 20*2^16
  parameter int SAMPLING_FREQUENCY = 44000
) (
  input logic clk,
  input logic reset,

  output logic                   recv_rdy,
  input  logic                   recv_val,
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES - 1:0],

  input  logic send_rdy,
  output logic send_val,
  output logic send_msg
);

  logic [BIT_WIDTH-1:0] in_mag[N_SAMPLES - 1:0];

  // Register for classifier input data
  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) classifier_in (
    .clk  (clk),
    .reset(reset),
    .d    (recv_msg),
    .q    (in_mag),
    .en   (recv_rdy && recv_val)
  );

  // Calculate the magnitude combinational
  logic [BIT_WIDTH-1:0] out_mag[N_SAMPLES - 1:0];

  magnitude_Magnitude#(
    .BIT_WIDTH (BIT_WIDTH),
    .DECIMAL_PT(DECIMAL_PT),
    .N_SAMPLES (N_SAMPLES),
  ) (
      .recv_msg(in_mag), .send_msg(out_mag)
  );

  // Register for magnitude output
  logic [BIT_WIDTH-1:0] out_mag_reg[N_SAMPLES - 1:0];

  cmn_ResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) mag_reg (
    .clk(clk),
    .reset(reset),
    .d(out_mag),
    .q(out_mag_reg)
  );

  // Filter based on cutoff

  logic [BIT_WIDTH-1:0] frequency_array [N_SAMPLES-1:0];
  
  frequency_arr #(
    .BIT_WIDTH         (BIT_WIDTH),
    .DECIMAL_PT        (DECIMAL_PT),
    .N_SAMPLES         (N_SAMPLES),
    .SAMPLING_FREQUENCY(SAMPLING_FREQUENCY)
  ) (
    .frequency_out(frequency_array)
  );

  logic [BIT_WIDTH-1:0] out_filter[N_SAMPLES - 1:0];

  highpass_Highpass#(
    .BIT_WIDTH  (BIT_WIDTH),
    .DECIMAL_PT (DECIMAL_PT),
    .N_SAMPLES  (N_SAMPLES),
    .CUTOFF_FREQ(CUTOFF_FREQ)
  ) (
      .freq_in(frequency_array),
      .mag_in(in_filter),
      .filtered_valid(out_filter)
  );

  // Register for classify 
  logic [BIT_WIDTH-1:0] out_highpass_reg[N_SAMPLES - 1:0];

  cmn_ResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) highpass_reg (
    .clk(clk),
    .reset(reset),
    .d(out_filter),
    .q(out_highpass_reg)
  );

  // Do comparison mag > cutoff_mag
  logic out_comparison;
  logic comparison_done;

  comparison_Comparison#(
    .BIT_WIDTH (BIT_WIDTH),
    .DECIMAL_PT(DECIMAL_PT),
    .N_SAMPLES (N_SAMPLES),
    .CUTOFF_MAG(CUTOFF_MAG)
  ) (
      .filtered_valid(out_highpass_reg),
      .mag_in(out_mag_reg),
      .compare_out(out_comparison),
      .done(comparison_done)
  );

  // Register for output
  logic on_off;
  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) classifier_in (
    .clk  (clk),
    .reset(reset),
    .d    (out_comparison),
    .q    (on_off),
    .en   (result_en)
  );

  assign send_msg = on_off;

  // FSM Control

  logic [1:0] currentState;
  logic [1:0] nextState;

  parameter [1:0] IDLE = 2'd0, CALC = 2'd1, DONE = 2'd3;

  // Next State Comb Logic
  always_comb begin
    case (currentState)
      IDLE: if (recv_rdy && recv_val) nextState = CALC;
 else nextState = IDLE;
      CALC: if (compare_done) nextState = CALC;
 else nextState = DONE;
      DONE: if (send_rdy && send_val) nextState = IDLE;
 else nextState = DONE;
      default: begin
        nextState = IDLE;
      end
    endcase
  end

  // Output Comb Logic
  always_comb begin
    case (currentState)
      IDLE: begin
        recv_rdy  = 1;
        send_val  = 0;
        result_en = 0;
      end
      CALC:
      if (comparison_done) begin
        recv_rdy  = 0;
        send_val  = 0;
        result_en = 1;
      end else begin
        recv_rdy  = 0;
        send_val  = 0;
        result_en = 0;
      end
      DONE: begin
        recv_rdy  = 0;
        send_val  = 1;
        result_en = 0;
      end
      default: begin
        recv_rdy  = 0;
        send_val  = 0;
        result_en = 0;
      end
    endcase
  end

  // State FFs
  always_ff @(posedge clk) begin
    if (reset) begin
      currentState <= IDLE;
    end else begin
      currentState <= nextState;
    end
  end

endmodule

`endif
