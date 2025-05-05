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
  logic                 magnitude_val [N_SAMPLES];
  
  //Purely for probing in simulation. Not used otherwise...
  logic                 bin_val [N_SAMPLES];          

  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
      assign magnitude_val[i] = mag_in[i] >= cutoff_mag;
      assign compare_outs[i] = filtered_valid[i] & magnitude_val[i];
      assign bin_val[i] = filtered_valid[i] & magnitude_val[i];
    end
  endgenerate

  assign compare_out = compare_outs != 0;
endmodule

`endif
