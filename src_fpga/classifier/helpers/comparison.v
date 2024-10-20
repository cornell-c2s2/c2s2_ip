//================================================
// comparison.v
//================================================
`default_nettype none
`ifndef COMPARISON_V
`define COMPARISON_V

module comparison_Comparison #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input  logic [BIT_WIDTH - 1:0] cutoff_mag,
  input  logic                   filtered_valid[N_SAMPLES],
  input  logic [BIT_WIDTH - 1:0] mag_in        [N_SAMPLES],
  output logic                   compare_out
);
  logic [N_SAMPLES-1:0] compare_outs;

  generate
    genvar i;
    for (i = 0; i < N_SAMPLES; i = i + 1) begin : for_loop
      assign compare_outs[i] = filtered_valid[i] & (mag_in[i] > cutoff_mag);
    end
  endgenerate

  assign compare_out = compare_outs != 0;
endmodule

`endif
