//================================================
// highpass.v
//================================================
`default_nettype none
`ifndef HIGHPASS_V
`define HIGHPASS_V

module highpass_Highpass #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input  logic [BIT_WIDTH - 1:0] cutoff_freq,
  input  logic [BIT_WIDTH - 1:0] freq_in       [N_SAMPLES],
  output logic                   filtered_valid[N_SAMPLES]
);

  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
      assign filtered_valid[i] = freq_in[i] > cutoff_freq;
    end
  endgenerate


endmodule

`endif
