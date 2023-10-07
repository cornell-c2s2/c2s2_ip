`ifndef FIXEDPT_SINE_WAVE
`define FIXEDPT_SINE_WAVE
`default_nettype none

// Macro to generate a sine table for N evenly spaced values from 0 to 2pi.
// Returns values in a fixedpoint format with D fractional bits and W total bits.
module SineWave #(
  parameter int N = 8,
  parameter int W = 32,
  parameter int D = 16
) (
  output logic [W - 1:0] sine_wave_out[0:N - 1]
);

  generate
    // arccos(-1) = pi
    real PI = $acos(-1);
    for (genvar i = 0; i < N; i++) begin
      real sinvalue = $sin(2 * PI * i / N);
      /* verilator lint_off UNUSED */
      int  fixedptvalue = $rtoi(sinvalue * (1 << D));
      /* verilator lint_on UNUSED */

      assign sine_wave_out[i] = fixedptvalue[W-1:0];
    end
  endgenerate

endmodule

`endif
