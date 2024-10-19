`ifndef fft_helpers_SINE_WAVE
`define fft_helpers_SINE_WAVE
`default_nettype none

// Macro to generate a sine table for N evenly spaced values from 0 to 2pi.
// Returns values in a fixedpoint format with D fractional bits and W total bits.
module fft_helpers_SineWave #(
  parameter int N = 8,
  parameter int W = 32,
  parameter int D = 16
) (
  output logic [W - 1:0] out[N]
);
  // arccos(-1) = pi
  //localparam real PI = $acos(-1); <- does not synthesize on quartus; replaced with line below
  localparam [31:0] PI = 32'd314159; // synthesis-specific code: fixed-point approx of pi

  // Checks on parameters to make sure behavior is well defined.
  generate
    if (D >= 32) begin
		//	$error("D must be less than 32"); <- does not synthesize on quartus; commented out for synthesis
	 end

    genvar i;
    for ( i = 0; i < N; i++) begin : for_loop
      localparam real sinvalue = $sin(2 * PI/65536 * i / N); // PI is scaled by 65536 for synthesis-specific code
      /* verilator lint_off UNUSED */
      int fixedptvalue = int'(sinvalue * 2.0 ** D);
      /* lint_on */

      assign out[i] = {{(W - D - 1) {fixedptvalue[31]}}, fixedptvalue[D:0]};
    end
  endgenerate

endmodule

`endif
