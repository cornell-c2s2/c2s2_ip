import wave
import numpy as np
from scipy.signal import resample
import os
import sys

current_dir = os.path.dirname(__file__)
src_root = os.path.abspath(os.path.join(current_dir, "../../../"))
sys.path.insert(0, src_root)

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory
from pymtl3 import *
from fixedpt import Fixed, CFixed
from src.classifier.sim import classify
from src.fft.tests.fft import FFTInterface, FFTPease
from tools.utils import fixed_bits

def wav_to_q8_8_messages(filename: str, normalization: int) -> bytes:
    with wave.open(filename, "rb") as wf:
        orig_rate = wf.getframerate()
        n_channels = wf.getnchannels()
        sampwidth = wf.getsampwidth()
        n_frames = wf.getnframes()
        raw = wf.readframes(n_frames * n_channels)

    if sampwidth == 3:
        raw_bytes = np.frombuffer(raw, dtype=np.uint8)
        if raw_bytes.size % 3 != 0:
            raise ValueError(f"Raw data size {raw_bytes.size} is not divisible by 3 for 24-bit audio.")

        num_samples_total = raw_bytes.size // 3
        reshaped_bytes = raw_bytes.reshape(num_samples_total, 3)

        samples_int32 = np.empty(num_samples_total, dtype=np.int32)
        samples_int32[:] = reshaped_bytes[:, 0]
        samples_int32 |= (reshaped_bytes[:, 1].astype(np.int32) << 8)
        samples_int32 |= (reshaped_bytes[:, 2].astype(np.int32) << 16)

        negative_mask = reshaped_bytes[:, 2] >= 0x80
        samples_int32[negative_mask] |= np.int32(~0xFFFFFF)

        samples = samples_int32
        dtype = np.int32
        n_frames = num_samples_total // n_channels

    elif sampwidth in [1, 2, 4]:
        dtype_map = {1: np.uint8, 2: np.int16, 4: np.int32}
        dtype = dtype_map[sampwidth]
        samples = np.frombuffer(raw, dtype=dtype)
        n_frames = len(samples) // n_channels
    else:
        raise ValueError(f"Unsupported sample width: {sampwidth}")

    if n_channels > 1:
        if samples.size % n_channels != 0:
            raise ValueError(f"Total samples {samples.size} not divisible by number of channels {n_channels}.")
        samples = samples.reshape(-1, n_channels).mean(axis=1).astype(dtype)

    if(normalization == 1):
        # Normalize to –1..+1
        if np.issubdtype(dtype, np.integer):
            max_val = float(2 ** (8 * sampwidth - 1))
            samples = samples.astype(np.float32) / max_val
        else:
            samples = samples.astype(np.float32)
        samples = np.clip(samples, -1.0, 1.0)
        
    # Convert to Q8.8 fixed‑point
    fixed = np.round(samples * (1 << 8)).astype(np.int16)

    return fixed.tolist()

raw_bytes = wav_to_q8_8_messages("input.wav", 0)
raw_bytes = raw_bytes[:32]
print("BYTES:")
for bytes in raw_bytes:
    print(hex(bytes))

N_CYCLES = 10

filtered_bytes = [byte for i, byte in enumerate(raw_bytes, start=1) if i % N_CYCLES != 0]

print("FILTERED BYTES:")
for filtered in filtered_bytes:
    print(hex(filtered))