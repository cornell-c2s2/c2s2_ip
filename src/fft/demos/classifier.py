from os import path
from matplotlib import gridspec
import matplotlib.pyplot as plt
from src.fft.demos.utils import plot_spectrogram, spectrogram, numpy_fft
import numpy as np
from halo import Halo
import librosa
import multiprocessing as mp
import argparse
import math

def run_spectrogram(sample_rate, file, cutoff_idx_low, cutoff_idx_high, cutoff_mag):

    print("RUN_SPECTOGRAM")

    n_samples = 32
    data, sample_rate = librosa.load(
        path.join(path.dirname(__file__), "audio", file), sr=sample_rate, mono=True
    )

    print("SPECTOGRAM")

    data, bins = spectrogram(
        numpy_fft,
        data,
        sample_rate,
        n_samples,
        n_samples - 4,
    )

    print("CLASSIFY")

    classified = classify(data, cutoff_idx_low, cutoff_idx_high, cutoff_mag)

    return data, classified


def classify(magnitudes: list[list[float]], low: int, high: int, threshold: float) -> list[bool]:

    count = 0
    classifications = []

    on_cycle = 0 # Consecutive cycles with magnitude above threshold
    off_cycle = 0 # Consecutive cycles with magnitude below threshold

    curr_sound = False # Whether or not we are on a sound

    convVert = 0
    convUpHalf = 0
    convLowHalf = 0

    for j, sample in enumerate(magnitudes):
        
        counter = 0

        max_mag = 0

        # Check if there is a bin with a magnitude above the threshold
        for i, mag in enumerate(sample):
            # Vertical convolution
            if (i > low):
                convVert += mag
            
            # Convolution for Upper Half (between 11350 - 20000)
            if (i > len(sample)//2): # consider dividing into thirds, multiplying middle by 2 and rest by 1
                convUpHalf += mag * 2
                convLowHalf -= mag * 2
                
            # Convolution for Lower Half (between 2700 - 11350)
            if (i < len(sample)//2): 
                convLowHalf += mag * 2
                convUpHalf -= mag * 2

            if mag > threshold:
                if i < low or i > high:
                    if (mag > max_mag):
                        max_mag = mag * 0.125
                    # Reduce magnitude outside the interval
                else:
                    if (mag * 20 > max_mag):
                        max_mag = mag * 16
                        
                    # Amplify magnitude within the interval
                    
                counter += 1
        if (counter == 0):
            classifications.append([0] * 7)
            continue
        if (max_mag > 0.5):
            on_cycle += 1
            off_cycle = 0

        elif (max_mag < 0.3):
            # TODO: need to add this to verilog
            if (curr_sound == False): # Resetting Convolutions 
                convVert = 0
                convUpHalf = 0
                convLowHalf = 0
            on_cycle = 0
            off_cycle += 1
        
        # When there are 300 cycles with a magnitude > 0.5, then curr_sound is true indicating we are on a sound
        if (on_cycle > 300):
            curr_sound = True
        
        # When 2000 cycles pass with magnitude < 0.3, then we get out of any sound we may be in
        elif (off_cycle > 2000):
            curr_sound = False
        
        if (curr_sound == True):
            if (convLowHalf > convVert):
                count = 10
        else:
            count = 0
        if (count > 0):
            count -= 1

        # classifications.append([max_mag, convVert, convUpHalf, convLowHalf, math.log2(max_mag), count, on_cycle])
        classifications.append(count>0)

    return classifications


if __name__ == "__main__":
    sample_rate = 44800

    audio_files = [
        "716U_U19_06_08_17_46_21.179-U19_06_08_17_47_26.568.wav", #Mostly empty sound except for beginning
        "409U_U19_06_08_12_11_41.016-U19_06_08_12_12_46.416.wav", #Shaking
        "557U_U19_06_08_14_52_58.187-U19_06_08_14_54_3.533.wav",  #Pulsing sound in bg
        "124U_U19_06_08_07_00_40.257-U19_06_08_07_01_45.848.wav", #Weird shaking with a couple bird calls
        "857U_U19_06_08_20_20_21.794-U19_06_08_20_21_27.370.wav", #Other bird call very audible, some scratching
        "033U_U19_06_08_05_21_11.070-U19_06_08_05_22_16.661.wav", #Bird making noise
        "SSR4F_MixPre-1390_01.wav", #Bird call
        "022U_U19_06_08_05_09_9.463-U19_06_08_05_10_15.070.wav", #Spaced out other bird call
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

        extra = 1
        if isinstance(group[0][2][0], list):
            extra = len(group[0][2][0])

        gs = gridspec.GridSpec(
            4 + extra,
            3,
            wspace=0.0,
            hspace=0.0,
            top=0.95,
            bottom=0.05,
            left=0.08,
            right=0.95,
        )

        plt.figure(figsize=(12, 5))

        for i, numpy_res in enumerate(group):
            # Give the first plot 4/5 slots
            ax = plt.subplot(gs[:4, i])
            plot_spectrogram(ax, sample_rate, numpy_res[0], numpy_res[1])
            if i == 0:
                ax.set_ylabel("Frequency (Hz)")
                ax.set_yticks(numpy_res[1][::2])

            xspace = np.linspace(
                0, 4 * len(numpy_res[0]) / sample_rate, len(numpy_res[0])
            )

            if isinstance(numpy_res[2][0], list):
                # Create a line plot in the bottom
                for j in range(len(numpy_res[2][0])):
                    tax = plt.subplot(gs[4+j, i])
                
                    tax.plot(
                        xspace,
                        [x[j] for x in numpy_res[2]],
                        label=str(j)
                    )

                    tax.set_xlim(0, max(xspace))

                    if i == 0 and j == len(numpy_res[2][0]) - 1:
                        tax.set_xlabel("Time (s)")
            else:
                # Create a line plot in the bottom
                ax = plt.subplot(gs[4, i])
                ax.plot(
                    xspace,
                    numpy_res[2],
                    "k",
                )
                ax.set_ylim(0, 1.5)
                ax.set_yticks([])
                ax.set_xlim(0, max(xspace))

                if i == 0:
                    ax.set_xlabel("Time (s)")

        plt.savefig(path.join(path.dirname(__file__), f"classifier_{gi}.png"), dpi=1000)

    spinner.succeed("Plots generated")
