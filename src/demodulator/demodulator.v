module demodulator #(
  parameter Width = 8,
  parameter N_Stages = 2,
  parameter OSR = 1250
) (
  input clk,
  input reset,
  input in,
  output reg [Width-1:0] demodulated_output,
  output reg adc_valid
);
  //prevent overflow
  localparam Internal_Width = Width + N_Stages * $clog2(OSR) + 4;

  // integrator registers
  reg signed [Internal_Width-1:0] integrator[0:N_Stages-1];

  // comb registers
  reg signed [Internal_Width-1:0] comb[0:N_Stages-1];
  reg signed [Internal_Width-1:0] comb_delay[0:N_Stages-1];

  reg [$clog2(OSR)-1:0] downsample_counter;
  reg signed [Internal_Width-1:0] filter_buffer[0:3];
  reg [1:0] filter_index;
  reg filter_valid;

  wire signed [Internal_Width-1:0] input_val;

  assign input_val = in ? 1 : -1;

  integer i;

  always @(posedge clk or posedge reset) begin
    if (reset) begin

      for (i = 0; i < N_Stages; i = i + 1) begin
        integrator[i] <= 0;
        comb[i] <= 0;
        comb_delay[i] <= 0;
      end

      for (i = 0; i < 4; i = i + 1) begin
        filter_buffer[i] <= 0;
      end

      filter_index <= 0;
      filter_valid <= 0;
      downsample_counter <= 0;
      adc_valid <= 1'b0;
      demodulated_output <= 0;
    end else begin
      // Integrator cascade (high rate)
      integrator[0] <= integrator[0] + input_val;
      for (i = 1; i < N_Stages; i = i + 1) begin
        integrator[i] <= integrator[i] + integrator[i-1];
      end

      // Decimation
      if (downsample_counter == OSR - 1) begin
        downsample_counter <= 0;

        // Comb filter cascade (runs at decimated rate)
        for (i = 0; i < N_Stages; i = i + 1) begin
          if (i == 0) begin
            comb[i] <= integrator[N_Stages-1] - comb_delay[i];
          end else begin
            comb[i] <= comb[i-1] - comb_delay[i];
          end
          comb_delay[i] <= (i == 0) ? integrator[N_Stages-1] : comb[i-1];
        end

        //  moving average buffer
        filter_buffer[filter_index] <= comb[N_Stages-1];
        filter_index <= filter_index + 1;
        filter_valid <= (filter_index == 3);

        if (filter_valid) begin
          demodulated_output <= (filter_buffer[0] + filter_buffer[1] + 
                                filter_buffer[2] + filter_buffer[3]) * 2 >>> 
                                (2);
        end

        adc_valid <= 1'b1;
      end else begin
        downsample_counter <= downsample_counter + 1;
        adc_valid <= 1'b0;
      end
    end
  end
endmodule
