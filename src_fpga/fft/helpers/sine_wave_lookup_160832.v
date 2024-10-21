// SINE WAVE OF BIT_WIDTH = 16, DECIMAL_PT =  8
// FOR FFT OF SIZE = 32
module fft_helpers_sine_wave_lookup_160832
   (
       output logic [16 - 1:0] sine_wave_out [0:32 - 1]
   );
   assign sine_wave_out[0] = 0;
   assign sine_wave_out[1] = 49;
   assign sine_wave_out[2] = 97;
   assign sine_wave_out[3] = 142;
   assign sine_wave_out[4] = 181;
   assign sine_wave_out[5] = 212;
   assign sine_wave_out[6] = 236;
   assign sine_wave_out[7] = 251;
   assign sine_wave_out[8] = 256;
   assign sine_wave_out[9] = 251;
   assign sine_wave_out[10] = 236;
   assign sine_wave_out[11] = 212;
   assign sine_wave_out[12] = 181;
   assign sine_wave_out[13] = 142;
   assign sine_wave_out[14] = 97;
   assign sine_wave_out[15] = 49;
   assign sine_wave_out[16] = 0;
   assign sine_wave_out[17] = -49;
   assign sine_wave_out[18] = -97;
   assign sine_wave_out[19] = -142;
   assign sine_wave_out[20] = -181;
   assign sine_wave_out[21] = -212;
   assign sine_wave_out[22] = -236;
   assign sine_wave_out[23] = -251;
   assign sine_wave_out[24] = -256;
   assign sine_wave_out[25] = -251;
   assign sine_wave_out[26] = -236;
   assign sine_wave_out[27] = -212;
   assign sine_wave_out[28] = -181;
   assign sine_wave_out[29] = -142;
   assign sine_wave_out[30] = -97;
   assign sine_wave_out[31] = -49;
endmodule