import matplotlib.pyplot as plt
from matplotlib import gridspec
import numpy as np
from halo import Halo
from src.fft.demos.utils import spectrogram, plot_spectrogram, numpy_fft, mk_hard_fft
import librosa
from os import path
import multiprocessing as mp
import argparse

if __name__ == "__main__":
    # Generates a single spectrogram.
    parser = argparse.ArgumentParser(description="Generate spectrogram")
    parser.add_argument(
        "--file",
        "-f",
        type=str,
        default="SSR4F_MixPre-1390_01.WAV",
        help="The file to generate the spectrogram from. The program will search in the audio folder.",
    )

    args = parser.parse_args()

    spinner = Halo(text="Loading audio file", spinner="dots")
    spinner.start()

    # Load the audio file
    audio_file = path.join(path.dirname(__file__), "audio", args.file)
    data, sample_rate = librosa.load(audio_file, sr=44800, mono=True)
    assert sample_rate == 44800
    spinner.succeed("Audio file loaded")

    spinner = Halo(text="Generating spectrogram", spinner="dots")
    spinner.start()

    # Generate the spectrogram
    nsamples = 32
    results, bins = spectrogram(numpy_fft, data, sample_rate, nsamples, nsamples - 4)

    spinner.succeed("Spectrogram generated")

    # Plot the actual audio file
    # make the plot wider
    plt.figure(figsize=(12, 4))
    # make this a violin plot
    ax = plt.subplot(111)
    timespace = np.linspace(0, len(data) / sample_rate, len(data))
    ax.plot(timespace, data, color="black")
    ax.set_title(args.file)
    ax.set_xlabel("Time (s)")
    ax.set_ylabel("Amplitude")
    plt.savefig(path.join(path.dirname(__file__), "audio.png"), dpi=300)

    plt.clf()

    # Plot the spectrogram
    plt.figure()
    ax = plt.subplot(111)
    plot_spectrogram(ax, sample_rate, results, bins, nsamples - 4)
    ax.set_ylabel(f"Frequency (Hz)")
    ax.set_yticks(bins[::2])
    ax.set_xlabel(f"Time (s)")
    ax.set_xlim(0, 4 * len(results) / sample_rate)
    ax.set_xticks(np.arange(0, 4 * len(results) / sample_rate, 1))

    ax.set_title(f"{nsamples}-sample FFT")
    # Save the plot
    plt.savefig(path.join(path.dirname(__file__), "spectrogram.png"), dpi=300)
