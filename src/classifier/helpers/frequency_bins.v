//================================================
// frequency_bins.v
//================================================
`default_nettype none
`ifndef FREQUENCY_BINS_V
`define FREQUENCY_BINS_V

// Calculates the frequency bins of an FFT
// Requires that N_SAMPLES is a power of 2
module classifier_helpers_FrequencyBins #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 16
) (
  input  logic [BIT_WIDTH - 1:0] sampling_freq,
  output logic [BIT_WIDTH - 1:0] frequency_out[N_SAMPLES]
);

  localparam int LOG2_N_SAMPLES = $clog2(N_SAMPLES);

  initial begin
    if ($pow(2, LOG2_N_SAMPLES) != N_SAMPLES) begin
      $error("N_SAMPLES must be a power of 2");
    end
  end

  // We make the sampling frequency a bit wider to avoid overflow
  wire [LOG2_N_SAMPLES + BIT_WIDTH - 1:0] wide_sampling_freq = {
    (LOG2_N_SAMPLES)'(0), sampling_freq
  };

  generate
    genvar i;
    for (i = 0; i < N_SAMPLES; i++) begin : gen_freq
      wire [LOG2_N_SAMPLES + BIT_WIDTH - 1:0] wide_freq_out = (i * wide_sampling_freq) >> (LOG2_N_SAMPLES + 1);
      assign frequency_out[i] = wide_freq_out[BIT_WIDTH-1:0];

      wire unused = &{1'b0, wide_freq_out[LOG2_N_SAMPLES+BIT_WIDTH-1:BIT_WIDTH], 1'b0};
    end
  endgenerate

endmodule

`endif
