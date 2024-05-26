# Simulation for the classifier
from fixedpt import Fixed
import numpy as np


# frequency bins for a given FFT
def frequency_bins(
    sampling_freq: int, n_samples: int, bit_width: int, decimal_pt: int
) -> list[Fixed]:
    # we double the number of samples to get enough bins
    bins = np.fft.rfftfreq(n_samples * 2, 1 / float(sampling_freq))

    # convert the bins to fixed point
    return [Fixed(x, True, bit_width, decimal_pt) for x in bins]
