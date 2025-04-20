"""
Testbench to test FFT on real data.
Input is a WAV file, the testbench sends the data over SPI and reads the FFT output back.
The testbench is parameterizable by sampling rate (in Hz). If the .wav file is multi-channel,
then it is averaged down to mono before sending it to the FFT.
"""

import wave
import numpy as np
from scipy.signal import resample


import random
from enum import Enum

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory
from pymtl3 import *
from fixedpt import Fixed, CFixed

from src.tapeins.sp25.tapein1.tests.test_top import fft1_msg, fft2_msg, reset_dut
from src.tapeins.sp25.tapein1.tests.spi_driver_sim import (
    spi_write_read,
    spi_write,
    spi_read,
)
from src.classifier.sim import classify
from src.fft.tests.fft import FFTInterface, FFTPease
from tools.utils import fixed_bits


# Parse a .wav file to Q8.8 fixed-point format
def wav_to_q8_8_messages(filename: str, target_rate: int) -> bytes:
    # 1)–3) same as before: open, read, channel‑mix, resample…
    with wave.open(filename, "rb") as wf:
        orig_rate = wf.getframerate()
        n_channels = wf.getnchannels()
        sampwidth = wf.getsampwidth()
        n_frames = wf.getnframes()
        raw = wf.readframes(n_frames)
    dtype_map = {1: np.uint8, 2: np.int16, 4: np.int32}
    dtype = dtype_map[sampwidth]
    samples = np.frombuffer(raw, dtype=dtype)
    if n_channels > 1:
        samples = samples.reshape(-1, n_channels).mean(axis=1).astype(dtype)
    if orig_rate != target_rate:
        new_len = int(len(samples) * target_rate / orig_rate)
        samples = resample(samples, new_len)

    # 4) Normalize to –1..+1
    if np.issubdtype(dtype, np.integer):
        max_val = float(2 ** (8 * sampwidth - 1))
        samples = samples.astype(np.float32) / max_val
    else:
        samples = samples.astype(np.float32)
    samples = np.clip(samples, -1.0, 1.0)

    # 5) Convert to Q8.8 fixed‑point (signed 16‑bit, 8 frac bits)
    #    multiply by 2^8, round, cast to int16
    fixed = np.round(samples * (1 << 8)).astype(np.int16)

    # return raw little‑endian bytes, or list(fixed) for Python ints
    return fixed.tolist()
