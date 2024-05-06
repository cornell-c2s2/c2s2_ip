`include "cmn/regs.v"
`include "classifier/helpers/classifier_regs.v"
`include "classifier/helpers/frequency_arr.v"

module kevin_classifier #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES = 8
)(
  input logic clk,
  input logic reset,

  output logic                   recv_rdy,
  input  logic                   recv_val,
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES - 1:0],

  output logic                   cutoff_freq_low_rdy,
  input  logic                   cutoff_freq_low_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_freq_low_msg,

  output logic                   cutoff_freq_high_rdy,
  input  logic                   cutoff_freq_high_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_freq_high_msg,

  output logic                   cutoff_mag_rdy,
  input  logic                   cutoff_mag_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_mag_msg,

  output logic                   sampling_freq_rdy,
  input  logic                   sampling_freq_val,
  input  logic [BIT_WIDTH - 1:0] sampling_freq_msg,

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
    .en   (recv_rdy && recv_val)
  );

  logic [BIT_WIDTH-1:0] low;

  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value({BIT_WIDTH{1'b0}})
  ) low_cutoff_freq_in (
    .clk  (clk),    
    .reset(reset), 
    .d    (cutoff_freq_low_msg),      
    .q    (low),          
    .en   (cutoff_freq_low_rdy && cutoff_freq_low_val)
  );

  logic [BIT_WIDTH-1:0] high;

  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value({BIT_WIDTH{1'b0}})
  ) high_cutoff_freq_in (
    .clk  (clk),    
    .reset(reset), 
    .d    (cutoff_freq_high_msg),      
    .q    (high),          
    .en   (cutoff_freq_high_rdy && cutoff_freq_high_val)
  );

  logic [BIT_WIDTH-1:0] threshold;

  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value({BIT_WIDTH{1'b0}})
  ) cutoff_mag_in (
    .clk  (clk),    
    .reset(reset), 
    .d    (cutoff_mag_msg),      
    .q    (threshold),          
    .en   (cutoff_mag_rdy && cutoff_mag_val)
  );

  logic [BIT_WIDTH-1:0] in_sampling_freq;

  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value({BIT_WIDTH{1'b0}})
  ) sampling_freq_in (
    .clk  (clk),    
    .reset(reset), 
    .d    (sampling_freq_msg),      
    .q    (in_sampling_freq),          
    .en   (sampling_freq_rdy && sampling_freq_val)
  );

  /////////////////////////////////////////////////////////////////////////////
  // Frequency array generator (bins)
  /////////////////////////////////////////////////////////////////////////////
  frequency_arr #(
    .BIT_WIDTH (BIT_WIDTH),
    .DECIMAL_PT(DECIMAL_PT),
    .N_SAMPLES (N_SAMPLES)
  ) freq_gen (
    .sampling_freq(in_sampling_freq),
    .frequency_out(frequency_array)
  );

  // TODO: not sure what these are supposed to be
  parameter UPPER_HALF_START = 11350 << DECIMAL_PT; // 11350 in fixed point
  parameter UPPER_HALF_END = 20000 << DECIMAL_PT;   // 20000 in fixed point

  logic [BIT_WIDTH-1:0] max_mag;
  logic [BIT_WIDTH-1:0] convVert;
  logic [BIT_WIDTH-1:0] convUpHalf;
  logic [BIT_WIDTH-1:0] convLowHalf;

  logic [31:0] on_cycle;
  logic [31:0] off_cycle;

  /////////////////////////////////////////////////////////////////////////////
  // FSM
  /////////////////////////////////////////////////////////////////////////////
  logic [1:0] classifier_state;

  parameter [1:0] IDLE = 2'd0, CALC = 2'd1, DONE = 2'd2;

  // Next state logic (calc is single cycle)
  always_ff @(posedge clk) begin
    if (reset) begin
      classifier_state <= IDLE;
    end else begin
      case (classifier_state)
        IDLE: begin 
          if (recv_rdy && recv_val) classifier_state <= CALC;
          else classifier_state <= IDLE; 
        end
        CALC: begin
          classifier_state <= DONE;
        end
        DONE: begin 
          if (send_rdy && send_val) classifier_state <= IDLE;
          else classifier_state <= DONE;
        end
        default: begin
          classifier_state <= classifier_state;
        end
      endcase
    end
  end


  // Data processing

  logic curr_sound;
  logic [31:0] count;
  logic [31:0] i;

  always_ff @(posedge clk) begin

    if (reset) begin
      on_cycle <= 0;
      off_cycle <= 0;
      count <= 0;
    end
    else begin
      case (classifier_state)

        IDLE: begin
          max_mag <= 0;
          convVert <= 0;
          convUpHalf <= 0;
          convLowHalf <= 0;
          curr_sound <= 0;
          on_cycle <= on_cycle;
          off_cycle <= off_cycle;
          count <= count;
        end

        CALC: begin

          max_mag <= 0;
          convVert <= 0;
          convUpHalf <= 0;
          convLowHalf <= 0;

          for (i = 0; i < NUM_SAMPLES; i = i + 1) begin

            // Vertical convolution
            if (bin[i] > low && bin[i] < high) begin
              convVert <= convVert + magnitude[i];
            end

            // Upper Half Convolution (TODO: not sure what upper half is)
            if (bin[i] > UPPER_HALF_START && bin[i] < UPPER_HALF_END) begin
              convUpHalf  <= convUpHalf + magnitude[i] >> 2;
              convLowHalf <= convLowHalf - magnitude[i] >> 2;
            end

            // Lower Half Convolution (TODO: not sure what lower half is)
            if (bin[i] > LOWER_HALF_START && bin[i] < LOWER_HALF_END) begin
              convLowHalf <= convLowHalf + magnitude[i] >> 2;
              convUpHalf  <= convUpHalf - magnitude[i] >> 2;
            end

            if (magnitude[i] > threshold) begin
              if (bin[i] < low || bin[i] > high) begin
                if (magnitude[i] > max_mag) begin
                  max_mag <= magnitude[i] / 10; // TODO: could modify to powers of 2
                end
              end else begin
                if (magnitude[i] * 20 > max_mag) begin
                  max_mag <= magnitude[i] * 20; // TODO: could modify to powers of 2
                end
              end
            end
          
          end

          if (max_mag > 0.5) begin  // TODO: 0.5 in fixed point
            on_cycle  <= on_cycle + 1;
            off_cycle <= 0;
          end 
          else if (max_mag < 0.3) begin  // TODO: 0.3 in fixed point
                                            // TODO: reset convolutions
            on_cycle  <= 0;
            off_cycle <= off_cycle + 1;
          end

          // TODO: not sure how to use on cycle across different data
          if (on_cycle > 300) begin
            curr_sound <= 1;
          end 
          else if (off_cycle > 2000) begin
            curr_sound <= 0;
          end

          // TODO: does 10 mean on? 
          if (curr_sound == 1 && convLowHalf > convVert) begin
              count <= 10
          end
          else begin
              count <= 0;
          end

          // TODO: not sure what this means
          if (count > 0) begin
              count <= count - 1;
          end

        end

        DONE: begin
          max_mag <= max_mag;
          convVert <= convVert;
          convUpHalf <= convUpHalf;
          convLowHalf <= convLowHalf;
          on_cycle <= on_cycle;
          off_cycle <= off_cycle;
          curr_sound <= curr_sound;
          count <= count;
        end

      endcase
  end

  assign send_msg = curr_sound;


  // Output Comb Logic for val/rdy

  always_comb begin
    case (currentState)
      IDLE: begin
        recv_rdy          = 1;
        cutoff_freq_rdy   = 1;
        cutoff_mag_rdy    = 1;
        sampling_freq_rdy = 1;
        send_val          = 0;
      end
      CALC: begin
        recv_rdy          = 0;
        cutoff_freq_rdy   = 0;
        cutoff_mag_rdy    = 0;
        sampling_freq_rdy = 0;
        send_val          = 0;
      end
      DONE: begin
        recv_rdy          = 0;
        cutoff_freq_rdy   = 0;
        cutoff_mag_rdy    = 0;
        sampling_freq_rdy = 0;
        send_val          = 1;
      end
      default: begin
        recv_rdy          = 0;
        cutoff_freq_rdy   = 0;
        cutoff_mag_rdy    = 0;
        sampling_freq_rdy = 0;
        send_val          = 0;
      end
    endcase
  end

endmodule
