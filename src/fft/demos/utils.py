import librosa
import matplotlib as mpl
import matplotlib.pyplot as plt
import os
from os import path
import numpy as np
from src.fft.pease.sim import fft as fft_sim
from fixedpt import CFixed


def spectrogram(
    fft: callable,
    data: list[list[float]],
    sample_rate: int,
    n_samples: int,
    n_overlap: int = None,
):
    """
    Generate a spectrogram from a wav file.

    Args:
        fig (matplotlib.Figure): Figure to plot to.
        ax (matplotlib.Axes): Axes to plot to.
        fft (callable): FFT function taking a list of floating point
            samples and returning a list of floating point results.
        wav (str): Path to wav file.
        n_samples (int): Number of samples.
        n_overlap (int): Number of overlap points between windows (defaults to n_samples // 8)
    """
    if n_overlap is None:
        n_overlap = n_samples // 8

    results = []

    for i in range(0, len(data) - n_samples, n_samples - n_overlap):
        sample = data[i : i + n_samples]
        if len(sample) < n_samples:
            break
        results.append(fft(sample)[: n_samples // 2])

    # Get the frequency bins
    bins = np.fft.fftfreq(n_samples, 1 / sample_rate)[: n_samples // 2]

    return results, bins


def plot_spectrogram(
    ax: mpl.axes.Axes,
    sample_rate: InterruptedError,
    data: list[list[float]],
    bins: list[float],
    n_overlap,
):
    n_samples = len(data[0]) * 2
    results = np.array(data).T
    ax.imshow(
        results,
        cmap="plasma",
        aspect="auto",
        origin="lower",
        extent=(
            0,
            (n_samples - n_overlap) * len(data) / sample_rate,
            bins[0],
            bins[-1],
        ),
    )

    # ax.set_xlabel("Time (s)")
    # ax.set_ylabel("Frequency (Hz)")
    # Remove axes
    ax.set_xticks([])
    ax.set_yticks([])


def numpy_fft(inputs: list[float]) -> list[float]:
    return np.abs(np.fft.fft(inputs))


def hard_fft(n: int, d: int, inputs: list[float]) -> list[float]:
    n_samples = len(inputs)
    # Convert inputs to CFixed
    inputs = [CFixed((x, 0), n, d) for x in inputs]

    outputs = fft_sim(inputs, n, d, n_samples)

    # Convert back to floats
    outputs = [complex(x) for x in outputs]

    return [abs(x) for x in outputs]


def mk_hard_fft(n: int, d: int, sim: bool) -> callable:
    return lambda inputs: hard_fft(n, d, inputs)
