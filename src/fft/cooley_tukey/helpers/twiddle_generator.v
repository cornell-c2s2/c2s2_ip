`ifndef TWIDDLE_GENERATOR
`define TWIDDLE_GENERATOR

/// Twiddle Generator module for a stage in a cooley tukey FFT
module TwiddleGenerator #(
  parameter int BIT_WIDTH  = 4,
  parameter int DECIMAL_PT = 2,
  parameter int SIZE_FFT   = 8,
  parameter int STAGE_FFT  = 0
) (
  input logic [BIT_WIDTH - 1:0] sine_wave_in[0:SIZE_FFT - 1],  //sine_wave_in = sin(2*pi m / N)

  output logic [BIT_WIDTH - 1:0] twiddle_real     [SIZE_FFT/2 - 1:0],
  output logic [BIT_WIDTH - 1:0] twiddle_imaginary[SIZE_FFT/2 - 1:0]
);

  logic [BIT_WIDTH - 1:0] t_real     [SIZE_FFT/2 - 1:0];
  logic [BIT_WIDTH - 1:0] t_imaginary[SIZE_FFT/2 - 1:0];

  generate
    for (genvar i = 0; i < SIZE_FFT/2; i = i + 1) begin
      assign t_real[i] = sine_wave_in[i+SIZE_FFT/4];
      assign t_imaginary[i] = sine_wave_in[i + SIZE_FFT/2];
    end
  endgenerate

  generate
    if(STAGE_FFT == 0) begin
      for (genvar i = 0; i < SIZE_FFT/2; i = i + 1) begin
        assign twiddle_real[i] = {{BIT_WIDTH-DECIMAL_PT-1{1'b0}},1'b1,{DECIMAL_PT{1'b0}}};
        assign twiddle_imaginary[i] = 0;
      end
    end
    else begin
      for (genvar m = 0; m < 2 ** STAGE_FFT; m = m + 1) begin
        for (genvar j = 0; j < 2 ** ($clog2(SIZE_FFT) - STAGE_FFT - 1); j = j + 1) begin
          int stageLeft = $clog2(SIZE_FFT) - STAGE_FFT - 1;
          int idx = m * (2 ** stageLeft);
          int si = idx + j;
          assign twiddle_real[si] = t_real[idx];
          assign twiddle_imaginary[si] = t_imaginary[idx];
        end
      end
    end

    // for (genvar m = 0; m < 2 ** STAGE_FFT; m = m + 1) begin
    //   for (genvar i = 0; i < SIZE_FFT; i = i + 2 ** (STAGE_FFT + 1)) begin
    //     // the index of the sine wave to use.
    //     int idx = m * SIZE_FFT / (1 << (STAGE_FFT + 1));

    //     assign twiddle_real[i/2+m] = sine_wave_in[(idx+SIZE_FFT/4)%SIZE_FFT];
    //     assign twiddle_imaginary[i/2+m] = -sine_wave_in[idx%SIZE_FFT];
    //   end
    // end
  endgenerate

endmodule

`endif
