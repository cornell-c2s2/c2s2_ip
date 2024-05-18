//================================================
// frequency_arr.v
//================================================
`default_nettype none
`ifndef FREQUENCY_ARR_V
`define FREQUENCY_ARR_V

module frequency_arr #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 16
) (
  input  logic [BIT_WIDTH - 1:0] sampling_freq,
  output logic [BIT_WIDTH - 1:0] frequency_out[N_SAMPLES - 1:0]
);

  localparam int LOG2_N_SAMPLES = $clog2(N_SAMPLES);

  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin : gen_freq
      if (LOG2_N_SAMPLES > DECIMAL_PT) begin
        assign frequency_out[i] = i * (sampling_freq >> (LOG2_N_SAMPLES - DECIMAL_PT));
      end else begin
        assign frequency_out[i] = i * (sampling_freq << (DECIMAL_PT - LOG2_N_SAMPLES));
      end
    end
  endgenerate

endmodule

`endif
