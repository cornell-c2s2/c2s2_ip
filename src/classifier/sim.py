# Simulation for the classifier
from fixedpt import Fixed
import numpy as np


# frequency bins for a given FFT
def frequency_bins(sampling_freq: int, n_samples: int) -> list[int]:
    # convert the bins to fixed point
    return [int(b) for b in np.fft.rfftfreq(n_samples * 2, 1 / float(sampling_freq))]


def classify(
    data: list[Fixed], cutoff_freq: int, cutoff_mag: Fixed, sampling_freq: int
) -> bool:
    bit_width = cutoff_mag._n
    decimal_pt = cutoff_mag._d

    assert all([d._n == bit_width for d in data])
    assert all([d._d == decimal_pt for d in data])

    # get the frequency bins
    bins = frequency_bins(sampling_freq, len(data))

    for i, d in enumerate(data):
        if bins[i] > cutoff_freq and abs(d) > cutoff_mag:
            return True

    return False
