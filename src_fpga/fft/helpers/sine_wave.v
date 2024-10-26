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
  localparam real PI = $acos(-1); // <- does not synthesize on quartus; replaced with line below
  // localparam [31:0] PI = 32'd314159; // synthesis-specific code: fixed-point approx of pi
  
  // logic [31:0] sine[32];
  // assign sine[0] = 32'd0;
  // assign sine[1] = 32'd12880;
  // assign sine[2] = 32'd25166;
  // assign sine[3] = 32'd36313;
  // assign sine[4] = 32'd46341;
  // assign sine[5] = 32'd54493;
  // assign sine[6] = 32'd60687;
  // assign sine[7] = 32'd64277;
  // assign sine[8] = 32'd65536;
  // assign sine[9] = 32'd64277;
  // assign sine[10] = 32'd60687;
  // assign sine[11] = 32'd54463;
  // assign sine[12] = 32'd46341;
  // assign sine[13] = 32'd36313;
  // assign sine[14] = 32'd25166;
  // assign sine[15] = 32'd12880;
  // assign sine[16] = 32'd0;
  // assign sine[17] = -32'd12880;
  // assign sine[18] = -32'd25166;
  // assign sine[19] = -32'd36313;
  // assign sine[20] = -32'd46341;
  // assign sine[21] = -32'd54493;
  // assign sine[22] = -32'd60687;
  // assign sine[23] = -32'd64277;
  // assign sine[24] = -32'd65536;
  // assign sine[25] = -32'd64277;
  // assign sine[26] = -32'd60687;
  // assign sine[27] = -32'd54463;
  // assign sine[28] = -32'd46341;
  // assign sine[29] = -32'd36313;
  // assign sine[30] = -32'd25166;
  // assign sine[31] = -32'd12880;

  // Checks on parameters to make sure behavior is well defined.
  generate
    // if (D >= 32) begin
	 //		$error("D must be less than 32"); // <- does not synthesize on quartus; commented out for synthesis
	 // end

    genvar i;
	  // logic [31:0] fixedptvalue;
    for ( i = 0; i < N; i++) begin : for_loop
      localparam real sinvalue = $sin(2 * PI * i / N); // PI is scaled by 65536 for synthesis-specific code
      /* verilator lint_off UNUSED */
      int fixedptvalue = int'(sinvalue * 2.0 ** D);
		// initial begin
		// 	fixedptvalue = (sine[i] * (2 ** D));
		// end
      /* lint_on */

      assign out[i] = {{(W - D - 1) {fixedptvalue[31]}}, fixedptvalue[D:0]};
    end
  endgenerate

endmodule

`endif
