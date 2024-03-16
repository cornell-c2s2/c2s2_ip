import matplotlib.pyplot as plt
from matplotlib import gridspec
import numpy as np
from halo import Halo
from src.fft.demos.utils import spectrogram, plot_spectrogram, numpy_fft, mk_hard_fft
import librosa
from os import path
import multiprocessing as mp
import argparse


# Runs a spectrogram with the given parameters
# This is necessary because we cannot directly pass functions into a process pool
# So instead we just pass the name and parameters of the function to this intermediate function
def run_spectrogram(f, data, sample_rate, n_samples, n_overlap):
    if f[0] == "numpy":
        f = numpy_fft
    else:
        f = mk_hard_fft(*f[1])
    results, bins = spectrogram(f, data, sample_rate, n_samples, n_overlap)
    return results, bins


if __name__ == "__main__":
    # Generates a grid of spectrograms comparing different bit widths and numbers of samples
    parser = argparse.ArgumentParser(description="Generate spectrogram grid")
    parser.add_argument(
        "--file",
        "-f",
        type=str,
        default="SSR1F_MixPre-1363.WAV",
        help="The file to generate the spectrogram from. The program will search in the audio folder.",
    )

    parser.add_argument(
        "--cache",
        "-c",
        action="store_true",
        help="If set, the program will not regenerate the spectrograms, but instead load them from the cache.",
    )

    args = parser.parse_args()

    # Check if the spectrograms have already been generated
    if args.cache and path.exists(
        path.join(path.dirname(__file__), "spectrogram_results.pkl")
    ):

        spinner = Halo(text="Generating spectrograms", spinner="dots")
        spinner.start()
        with open(
            path.join(path.dirname(__file__), "spectrogram_results.pkl"), "rb"
        ) as f:
            import pickle

            results = pickle.load(f)
        spinner.succeed("Spectrograms loaded")
    else:
        sample_rate = 44800

        wav_file = path.join(path.dirname(__file__), "audio", args.file)
        spinner = Halo(text="Loading audio file", spinner="dots")
        spinner.start()
        data = librosa.load(wav_file, sr=sample_rate, mono=True)[0]
        spinner.succeed("Audio file loaded")

        spinner = Halo(text="Generating spectrograms", spinner="dots")
        spinner.start()

        # Generate all the spectrograms in parallel
        with mp.Pool(16) as pool:
            results = pool.starmap(
                run_spectrogram,
                sum(
                    [
                        [(["numpy", None], data, sample_rate, n_samples, n_samples - 4)]
                        + [
                            (
                                ["hard", (*n_bits, True)],
                                data,
                                sample_rate,
                                n_samples,
                                0,
                            )
                            for n_bits in [(4, 2), (8, 4), (12, 8), (16, 12)]
                        ]
                        for n_samples in [8, 16, 32, 64]
                    ],
                    [],
                ),
            )

        # Pickle the results
        with open(
            path.join(path.dirname(__file__), "spectrogram_results.pkl"), "wb"
        ) as f:
            import pickle

            pickle.dump(results, f)

        spinner.succeed("Spectrograms generated")

    # Plot the spectrograms
    plt.figure()
    plt.rcParams.update({"font.size": 8})

    gs = gridspec.GridSpec(
        4,
        5,
        wspace=0.0,
        hspace=0.0,
        top=0.95,
        bottom=0.05,
        left=0.05,
        right=0.95,
    )

    ylabels = [8, 16, 32, 64]
    xlabels = [
        "numpy",
        "4 bits, 2 decimal",
        "8 bits, 4 decimal",
        "12 bits, 8 decimal",
        "16 bits, 12 decimal",
    ]

    for i, (result, bins) in enumerate(results):
        print(min(min(x) for x in result), max(max(x) for x in result))
        ax = plt.subplot(gs[i // 5, i % 5])
        plot_spectrogram(ax, sample_rate, result, bins)
        if i % 5 == 0:
            ax.set_ylabel(f"{ylabels[i//5]} samples")

        if i // 5 == 3:
            ax.set_xlabel(xlabels[i % 5])

    plt.savefig(path.join(path.dirname(__file__), "spectrograms.png"), dpi=300)
