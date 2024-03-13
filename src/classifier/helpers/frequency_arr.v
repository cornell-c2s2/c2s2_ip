//================================================
// frequency_arr.v
//================================================
`default_nettype none
`ifndef FREQUENCY_ARR_V
`define FREQUENCY_ARR_V

module frequency_arr #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES = 16,
  parameter int SAMPLING_FREQUENCY = 50000
) (
  output logic [BIT_WIDTH - 1:0] frequency_out[N_SAMPLES - 1:0]
);

  localparam int SCALING_FACTOR = 1 << DECIMAL_PT;
  localparam int FREQUENCY_STEP = SAMPLING_FREQUENCY / N_SAMPLES;

  genvar i;
  generate
    for (i = 0; i < N_SAMPLES; i++) begin : gen_freq
      // Calculating index for frequency bin, considering positive and negative frequencies.
      localparam int index = (i < N_SAMPLES / 2) ? i : i - N_SAMPLES;
      // Assigning pre-calculated frequency values to the output array.
      assign frequency_out[i] = (index * FREQUENCY_STEP) << DECIMAL_PT;
    end
  endgenerate

endmodule

`endif
