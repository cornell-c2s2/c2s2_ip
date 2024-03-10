//================================================
// highpass.v
//================================================
`default_nettype none
`ifndef HIGHPASS_V
`define HIGHPASS_V

module highpass_Highpass #(
  parameter int BIT_WIDTH   = 32,
  parameter int DECIMAL_PT  = 16,
  parameter int N_SAMPLES   = 8,
  parameter int CUTOFF_FREQ = 1000
) (
  input  logic [BIT_WIDTH - 1:0] freq_in       [N_SAMPLES - 1:0],
  output logic [BIT_WIDTH - 1:0] filtered_valid[N_SAMPLES - 1:0]
);

  genvar i;
  generate
    for (i = 0; i < N_SAMPLES; i = i + 1) begin
      assign filtered_valid[i] = (freq_in[i] > CUTOFF_FREQ);
    end
  endgenerate


endmodule

`endif
