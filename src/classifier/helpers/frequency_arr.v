//================================================
// frequency_arr.v
//================================================
`default_nettype none
`ifndef FREQUENCY_ARR_V
`define FREQUENCY_ARR_V

module frequency_arr #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES = 8,
  parameter int SAMPLING_FREQUENCY = 44000
) (
  output logic [BIT_WIDTH - 1:0] frequency_out[N_SAMPLES - 1:0]
);

  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin

      int value = (i / N_SAMPLES) * (1 / SAMPLING_FREQUENCY);
      int fixedptvalue = $rtoi(value * (1 << DECIMAL_PT));

      assign frequency_out[i] = fixedptvalue[BIT_WIDTH-1:0];
    end
  endgenerate

endmodule

`endif
