//================================================
// frequency_bins.v
//================================================
`default_nettype none
`ifndef FREQUENCY_BINS_V
`define FREQUENCY_BINS_V

module classifier_helpers_FrequencyBins #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 16
) (
  input  logic [BIT_WIDTH - 1:0] sampling_freq,
  output logic [BIT_WIDTH - 1:0] frequency_out[N_SAMPLES]
);

  localparam int LOG2_N_SAMPLES = $clog2(N_SAMPLES);

  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin : gen_freq
      if (LOG2_N_SAMPLES - DECIMAL_PT + 1 >= 0) begin
        assign frequency_out[i] = i * (sampling_freq >> (LOG2_N_SAMPLES - DECIMAL_PT + 1));
      end else begin
        assign frequency_out[i] = i * (sampling_freq << (DECIMAL_PT - LOG2_N_SAMPLES - 1));
      end
    end
  endgenerate

endmodule

`endif
