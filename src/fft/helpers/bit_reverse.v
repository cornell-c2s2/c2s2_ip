`ifndef FFT_BIT_REVERSAL
`define FFT_BIT_REVERSAL
`default_nettype none

/// FFT Bit Reversal
/// @param BIT_WIDTH  : Data bit width
/// @param N_SAMPLES   : Number of points in the FFT
module BitReverse #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input  logic [BIT_WIDTH - 1:0] in [N_SAMPLES],
  output logic [BIT_WIDTH - 1:0] out[N_SAMPLES]
);
  // number of bits in an index
  localparam int n = $clog2(N_SAMPLES);

  generate
    for (genvar m = 0; m < N_SAMPLES; m++) begin
      logic [n-1:0] m_rev;
      for (genvar i = 0; i < n; i++) begin
        assign m_rev[n-i-1] = m[i];
      end

      assign out[m_rev] = in[m];
    end
  endgenerate

endmodule

`endif
