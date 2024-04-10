More documentation available at [Confluence](https://confluence.cornell.edu/display/c2s2/FFT+and+Classifier+Demos).

# File setup

Files will be created in the demos directory.

Place audio files in the `audio/` folder.

# `spectrogram-grid.py`

Run `src/fft/demos/spectrogram_grid.py` to generate the spectrograms.

Output image will be generated in the `spectrograms.png` file.

## Arguments
* `--cache` or `-c`
  * This will use a cached version of the spectrograms to regenerate the plots. This is useful because calculating the spectrograms is pretty slow. Don't use this if you change the audio file.
* `--file` or `-f`
  * The audio file to generate spectrograms for.

# `classifier.py`

Run `src/fft/demos/classifier.py` to generate the outputs.

The outputs will be generated in `classifier_<index>.png`, each image will have spectrograms with classifier data from `3` different audio files.

The audio files used can be modified in the `audio_files` variable in the python file.