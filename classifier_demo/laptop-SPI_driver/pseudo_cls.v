


// iterate over each fft bin and check frequency and magnitude
for ( int i = 0; i < 16; i += 1 ) begin
  if ((fft_freq[i] > cutoff_freq) && (fft_mag[i] > cutoff_mag))
    classifier_out = 1;
  else
    classifier_out = 0;
end