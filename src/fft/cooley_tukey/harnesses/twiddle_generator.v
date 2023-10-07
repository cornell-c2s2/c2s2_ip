`include "src/fft/helpers/sine_wave.v"
`include "src/fft/helpers/cooley_tukey/twiddle_generator.v"

module TwiddleGeneratorHarness #(
  parameter int BIT_WIDTH  = 4,
  parameter int DECIMAL_PT = 1,
  parameter int SIZE_FFT   = 8,
  parameter int STAGE_FFT  = 0
) (

  output logic [BIT_WIDTH * SIZE_FFT - 1:0] send_msg
);

  logic [BIT_WIDTH - 1:0] sine_wave_out[0:SIZE_FFT - 1];
  logic [BIT_WIDTH - 1:0] twiddle_out  [SIZE_FFT - 1:0];

  generate
    for (genvar i = 0; i < SIZE_FFT; i = i + 1) begin
      assign send_msg[BIT_WIDTH*i+:BIT_WIDTH] = twiddle_out[i][BIT_WIDTH-1:0];
    end
  endgenerate

  SineWave #(
    .W(BIT_WIDTH),
    .D(DECIMAL_PT),
    .N(SIZE_FFT)
  ) sine_wave (
    .sine_wave_out(sine_wave_out)
  );

  TwiddleGenerator #(
    .BIT_WIDTH (BIT_WIDTH),
    .DECIMAL_PT(DECIMAL_PT),
    .SIZE_FFT  (SIZE_FFT),
    .STAGE_FFT (STAGE_FFT)
  ) twiddle_generator (
    .sine_wave_in(sine_wave_out),
    .twiddle_imaginary(twiddle_out[SIZE_FFT/2-1:0]),
    .twiddle_real(twiddle_out[SIZE_FFT-1:SIZE_FFT/2])
  );
endmodule
