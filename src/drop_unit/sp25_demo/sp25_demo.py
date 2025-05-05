import random
import os
import sys
import wave
from scipy.signal import resample

current_dir = os.path.dirname(__file__)
src_root = os.path.abspath(os.path.join(current_dir, "../../../"))
sys.path.insert(0, src_root)

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from dropunit_sim import wav_to_q8_8_messages, drop_bytes
from src.fft.pease.sim import fft
from fixedpt import Fixed, CFixed
from src.fft.tests.fft import FFTInterface, FFTPease
from cocotb.binary import BinaryValue

import matplotlib.pyplot as plt
import numpy as np

# parameters
NUM_BITS = 16
FFT_ARRAY_SIZE = 32

DROP_RATE = 20

raw_bytes = wav_to_q8_8_messages("input.wav", 0)
raw_bytes = raw_bytes[:len(raw_bytes)//(DROP_RATE * FFT_ARRAY_SIZE) * (DROP_RATE * FFT_ARRAY_SIZE) - 1]
raw_bytes = raw_bytes[:6399]
print("raw bytes")
print(raw_bytes[0:32])
downsampled_bytes = drop_bytes(raw_bytes, DROP_RATE)

fft_outputs = []


def int_to_twos_complement(value, num_bits=NUM_BITS):
    if value < 0:
        value = (1 << num_bits) + value
    return format(value, f'0{num_bits}b')


def analyze_real_fft_output(fft_out: list, is_external: int):
    """
    Analyze the real part of the FFT output and compare to frequency bins.
    
    Args:
        fft_out (list of Fixed): FFT output with only real parts (Fixed(16,8)).
        sample_rate (float): Sampling rate of the original signal.
    """
    n = len(fft_out)  # Number of FFT points

    freqs = np.fft.fftfreq(n, d=1/(96000/DROP_RATE))  # frequency bins
    magnitudes = []

    for c in fft_out:
        real = c.real.get(True) / (1 << 8)
        #imag = c.imag.get(True) / (1 << 8)
        #mag = (real**2 + imag**2)**0.5
        magnitudes.append(real)

    plt.figure(figsize=(10, 5))
    plt.plot(freqs[:n//2], magnitudes[:n//2])  # Only positive frequencies
    plt.title("FFT Magnitude Spectrum")
    plt.xlabel("Frequency (Hz)")
    plt.ylabel("Magnitude")
    plt.grid(True)
    if(is_external == 1):
        plt.savefig(f"external_bins{DROP_RATE}.png")
    else:
        plt.savefig(f"bins{DROP_RATE}.png")


@cocotb.test()
async def demo_check_drop(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    dut.reset.value = 1
    dut.enable.value = 0
    dut.enable_val.value = 1
    await ClockCycles(dut.clk, 1)

    dut.reset.value = 0
    dut.enable_val.value = 0

    dut.cfg_drop_val.value = 1
    dut.cfg_drop_msg.value = DROP_RATE 
    await ClockCycles(dut.clk, 1)
    
    dut.resp_rdy.value = 1
    
    for i in range(len(raw_bytes)):
        while dut.req_rdy.value == 0:
            await ClockCycles(dut.clk, 1)

        v = BinaryValue(n_bits=NUM_BITS, binaryRepresentation=2)
        v.binstr = int_to_twos_complement(raw_bytes[i])
        dut.req_msg.value = v
        dut.req_val.value = 1
        await ClockCycles(dut.clk, 1)
        
        if dut.drop_unit.resp_val.value == 1:
            av = BinaryValue(n_bits=NUM_BITS, binaryRepresentation=2)
            av.binstr = int_to_twos_complement(downsampled_bytes[i//DROP_RATE])
            assert dut.drop_unit.resp_msg.value == av
        if dut.resp_val.value == 1:
            fft_outputs.append(CFixed(v=(dut.resp_msg.value.integer, 0), n=NUM_BITS, d=8, raw=True))

    analyze_real_fft_output(fft_outputs[0:16], 0)
    print(fft_outputs[0:16])


'''
EXTERNAL MODEL
'''

def wav_to_q8_8_external(filename: str, target_rate: int) -> bytes:
    # 1)–3) same as before: open, read, channel‑mix, resample…
    with wave.open(filename, "rb") as wf:
        orig_rate = wf.getframerate()
        n_channels = wf.getnchannels()
        sampwidth = wf.getsampwidth()
        n_frames = wf.getnframes()
        # Read all raw bytes for all channels and frames
        raw = wf.readframes(n_frames * n_channels)

    # Process raw bytes based on sample width
    if sampwidth == 3:
        # Handle 24-bit audio (3 bytes)
        raw_bytes = np.frombuffer(raw, dtype=np.uint8)
        if raw_bytes.size % 3 != 0:
            raise ValueError(
                f"Raw data size {raw_bytes.size} is not divisible by 3 for 24-bit audio."
            )

        num_samples_total = raw_bytes.size // 3
        reshaped_bytes = raw_bytes.reshape(num_samples_total, 3)

        # Convert 3 bytes (little-endian) to signed int32
        samples_int32 = np.empty(num_samples_total, dtype=np.int32)
        samples_int32[:] = reshaped_bytes[:, 0]  # LSB
        samples_int32 |= reshaped_bytes[:, 1].astype(np.int32) << 8
        samples_int32 |= reshaped_bytes[:, 2].astype(np.int32) << 16  # MSB

        # Sign extend negative values (check MSB of the third byte)
        negative_mask = reshaped_bytes[:, 2] >= 0x80
        # Fill the most significant byte with 1s for negative numbers
        samples_int32[negative_mask] |= np.int32(~0xFFFFFF)  # or np.int32(0xFF000000)

        # Assign the processed samples and set dtype for downstream consistency
        samples = samples_int32
        dtype = np.int32
        # Calculate n_frames based on the total samples and channels
        n_frames = num_samples_total // n_channels

    elif sampwidth in [1, 2, 4]:
        # Handle standard sample widths
        dtype_map = {1: np.uint8, 2: np.int16, 4: np.int32}
        dtype = dtype_map[sampwidth]
        # Convert raw bytes to samples using the appropriate dtype
        samples = np.frombuffer(raw, dtype=dtype)
        # Calculate n_frames based on the total samples and channels
        n_frames = len(samples) // n_channels
    else:
        raise ValueError(f"Unsupported sample width: {sampwidth}")

    if n_channels > 1:
        # Reshape requires the total number of samples to be divisible by n_channels
        if samples.size % n_channels != 0:
            raise ValueError(
                f"Total samples {samples.size} not divisible by number of channels {n_channels}."
            )
        samples = samples.reshape(-1, n_channels).mean(axis=1).astype(dtype)
        print(samples[0:32])
    if orig_rate != target_rate:
        new_len = int(len(samples) * target_rate / orig_rate)
        samples = resample(samples, new_len)

    # 4) Normalize to –1..+1
    '''
    if np.issubdtype(dtype, np.integer):
        max_val = float(2 ** (8 * sampwidth - 1))
        samples = samples.astype(np.float32) / max_val
    else:
        samples = samples.astype(np.float32)
    samples = np.clip(samples, -1.0, 1.0)
    '''

    # 5) Convert to Q8.8 fixed‑point (signed 16‑bit, 8 frac bits)
    #    multiply by 2^8, round, cast to int16
    fixed = np.round(samples * (1 << 8)).astype(np.int16)

    # return raw little‑endian bytes, or list(fixed) for Python ints
    return fixed.tolist()

external_raw_bytes = wav_to_q8_8_external("input.wav", (96000/DROP_RATE))
external_raw_bytes = external_raw_bytes[0:32]

model = FFTPease(16, 8, 32)
golden = model.transform([CFixed(v=(s, 0), n=16, d=8) for s in external_raw_bytes])
fixed_outputs = [Fixed(x.real, True, 16, 8) for x in golden]
analyze_real_fft_output(golden[0:16], 1)
