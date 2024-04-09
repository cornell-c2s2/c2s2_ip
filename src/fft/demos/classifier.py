from os import path
from matplotlib import gridspec
import matplotlib.pyplot as plt
from src.fft.demos.utils import plot_spectrogram, spectrogram, numpy_fft
import numpy as np
from halo import Halo
import librosa
import multiprocessing as mp
import argparse


def run_spectrogram(sample_rate, file):
    n_samples = 32
    data, sample_rate = librosa.load(
        path.join(path.dirname(__file__), "audio", file), sr=sample_rate, mono=True
    )

    data, bins = spectrogram(
        numpy_fft,
        data,
        sample_rate,
        n_samples,
        n_samples - 4,
    )

    classified = classify(data, bins)

    return data, bins, classified


def classify(magnitudes: list[list[float]], bins: list[float]) -> list[bool]:
    # Cutoff values for frequency
    low = 2000
    high = 10000

    # Magnitude threshold
    threshold = 0.5

    count = 0
    classifications = []
    for i, sample in enumerate(magnitudes):
        # Check if there is a bin with a magnitude above the threshold
        for i, mag in enumerate(sample):
            if bins[i] < low or bins[i] > high:
                continue
            if mag > threshold:
                count = 44800
                break

        if count > 0:
            count -= 1
        classifications.append(count > 0)

    return classifications


if __name__ == "__main__":
    sample_rate = 44800

    audio_files = [
        # "SSR4F_MixPre-1390_01.WAV",
        "LHR1F_MixPre-1312_01.WAV",
        "SSR1F_MixPre-1363.WAV",
        "SSF1F_MixPre-2237_01.WAV",
        "SHI1F_MixPre-1620_01.WAV",
        "OS1F_MixPre-1472_01.WAV",
        "TIP1F_MixPre-1026.WAV",
        "rainstorm.wav",
        "wind.wav",
    ]

    # Check if the spectrograms have already been generated
    spinner = Halo(text="Generating spectrograms", spinner="dots")
    spinner.start()

    # Generate all the spectrograms in parallel
    with mp.Pool(16) as pool:
        results = pool.starmap(
            run_spectrogram, [(sample_rate, file) for file in audio_files]
        )

    spinner.succeed("Spectrograms generated")

    spinner = Halo(text="Generating plots", spinner="dots")
    spinner.start()

    # Split into groups of 3
    results = [results[i : i + 3] for i in range(0, len(results), 3)]
    for gi, group in enumerate(results):
        plt.clf()

        gs = gridspec.GridSpec(
            5,
            1,
            wspace=0.0,
            hspace=0.0,
            top=0.95,
            bottom=0.05,
            left=0.08,
            right=0.95,
        )

        # plt.figure(figsize=(12, 5))

        for i, numpy_res in enumerate(group):
            # Give the first plot 4/5 slots
            ax = plt.subplot(gs[:4, i])
            n_samples = len(numpy_res[0]) * 2
            plot_spectrogram(ax, sample_rate, numpy_res[0], numpy_res[1], n_samples - 4)
            if i == 0:
                ax.set_ylabel("Frequency (Hz)")
                ax.set_yticks(numpy_res[1][::2])

            # Create a line plot in the bottom
            ax = plt.subplot(gs[4, i])

            xspace = np.linspace(
                0, 4 * len(numpy_res[0]) / sample_rate, len(numpy_res[0])
            )
            ax.plot(
                xspace,
                numpy_res[2],
                "k",
            )

            ax.set_xlim(0, max(xspace))
            ax.set_ylim(0, 1.5)

            if i == 0:
                ax.set_xlabel("Time (s)")
            ax.set_yticks([])

        plt.savefig(path.join(path.dirname(__file__), f"classifier_{gi}.png"), dpi=300)

    spinner.succeed("Plots generated")
