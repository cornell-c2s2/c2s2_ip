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
  input  logic [BIT_WIDTH - 1:0] in [N_SAMPLES - 1:0],
  output logic [BIT_WIDTH - 1:0] out[N_SAMPLES - 1:0]
);
  // stores the reversed indexes
  int reversed_indexes[N_SAMPLES];
  // number of bits in an index
  int n = $clog2(N_SAMPLES);
  initial begin
    for (int m = 0; m < N_SAMPLES; m++) begin
      reversed_indexes[m] = 0;
      // loops through the bits in m and reverses them.
      for (int i = 0; i < n; i++) begin
        reversed_indexes[m] |= ((m >> i) & 1) << (n - i - 1);
      end
    end
  end

  generate
    for (genvar m = 0; m < N_SAMPLES; m++) begin
      assign out[reversed_indexes[m]] = in[m];
    end
  endgenerate

endmodule

`endif
