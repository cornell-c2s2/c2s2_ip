"""
Testbench to test FFT on real data.
Input is a WAV file, the testbench sends the data over SPI and reads the FFT output back.
The testbench is parameterizable by sampling rate (in Hz). If the .wav file is multi-channel,
then it is averaged down to mono before sending it to the FFT.
"""
import wave
import numpy as np
from scipy.signal import resample
import matplotlib.pyplot as plt

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory
from pymtl3 import *
from fixedpt import Fixed, CFixed
from src.classifier.sim import classify
from src.fft.tests.fft import FFTInterface, FFTPease
from tools.utils import fixed_bits

from src.tapeins.sp25.tapein1.tests.test_top import (
    run_top, reset_dut, fft1_msg, mk_spi_pkt, RouterOut,
    InXbarCfg, ClsXbarCfg, OutXbarCfg, ArbiterIn
)

# Parse a .wav file to Q8.8 fixed-point format
def wav_to_q8_8_messages(filename: str, target_rate: int) -> bytes:
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
            raise ValueError(f"Raw data size {raw_bytes.size} is not divisible by 3 for 24-bit audio.")

        num_samples_total = raw_bytes.size // 3
        reshaped_bytes = raw_bytes.reshape(num_samples_total, 3)

        # Convert 3 bytes (little-endian) to signed int32
        samples_int32 = np.empty(num_samples_total, dtype=np.int32)
        samples_int32[:] = reshaped_bytes[:, 0]  # LSB
        samples_int32 |= (reshaped_bytes[:, 1].astype(np.int32) << 8)
        samples_int32 |= (reshaped_bytes[:, 2].astype(np.int32) << 16) # MSB

        # Sign extend negative values (check MSB of the third byte)
        negative_mask = reshaped_bytes[:, 2] >= 0x80
        # Fill the most significant byte with 1s for negative numbers
        samples_int32[negative_mask] |= np.int32(~0xFFFFFF) # or np.int32(0xFF000000)

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
             raise ValueError(f"Total samples {samples.size} not divisible by number of channels {n_channels}.")
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

# Generate a sine wave at a given frequency and duration, then save it as a mono 16-bit WAV file.
def generate_sine_wav(filename, freq, duration, sampling_rate, amplitude=1):
    # Create time axis
    t = np.linspace(0, duration, int(sampling_rate * duration), endpoint=False)
    # Generate sine wave samples
    samples = amplitude * np.sin(2 * np.pi * freq * t)
    # Convert to 16-bit WAV
    audio = np.int16(samples * 32767)

    # Write to WAV file
    with wave.open(filename, "w") as wf:
        wf.setnchannels(1)  # mono
        wf.setsampwidth(2)  # 2 bytes for int16
        wf.setframerate(sampling_rate)
        wf.writeframes(audio.tobytes())


# Helper to plot FFT outputs
def plot_fft_outputs(fixed_outputs, title="FFT Outputs", filename=None):
    values = [float(x) for x in fixed_outputs]
    plt.figure()
    plt.stem(range(len(values)), values)
    plt.title(title)
    plt.xlabel("Bin")
    plt.ylabel("Amplitude")
    plt.grid(True)
    plt.tight_layout()
    if filename:
        plt.savefig(filename)
        plt.close()
    else:
        plt.show()

# Helper to plot FFT outputs and SPI output messages on separate graphs
def plot_fft_outputs_dual(fixed_inputs, fixed_outputs, title="FFT Outputs", filename_prefix=None):
    values1 = [int(x) for x in fixed_inputs]
    values2 = [int(x) for x in fixed_outputs]

    fig, axs = plt.subplots(2, 1, figsize=(8, 6))
    fig.suptitle(title)

    # Plot input amplitudes
    axs[0].plot(range(len(values1)), values1, 'b-o', label='Input')
    axs[0].set_xlabel("Sample Number")
    axs[0].set_ylabel("Input Amplitude")
    axs[0].set_title("Inputs")
    axs[0].grid(True)

    # Plot output amplitudes
    axs[1].plot(range(len(values2)), values2, 'r-x', label='Output')
    axs[1].set_xlabel("Bin Number")
    axs[1].set_ylabel("Output Amplitude")
    axs[1].set_title("Outputs")
    axs[1].grid(True)

    plt.tight_layout(rect=[0, 0.03, 1, 0.95])
    if filename_prefix:
        plt.savefig(f"{filename_prefix}_dual.png")
        plt.close()
    else:
        plt.show()

"""
================================================================================
FFT REAL DATA TESTS
================================================================================
"""


@cocotb.test()
async def test_fft1_with_wav(dut):
    # generate_sine_wav("input.wav", 5000, 0.01, 48000, amplitude=0.01)
    # drive the clock and reset
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)

    # load & quantize the first 32 samples as Q8.8 int16
    raw_bytes = wav_to_q8_8_messages("input.wav", target_rate=48000)
    dut._log.info(f"Number of samples: {len(raw_bytes)}")
    raw_bytes = raw_bytes[:32]
    # wrap them as Fixed(16,8) so fft1_msg can bit‑pack them
    fixed_inputs = [Fixed(s , True, 16, 8) for s in raw_bytes]
    dut._log.info(f"FFT inputs (fixed-point): {fixed_inputs}")

    # compute golden with FFTPease
    model = FFTPease(16, 8, 32)
    golden = model.transform(
        [CFixed(v=(s, 0), n=16, d=8) for s in raw_bytes]
    )
    # we only compare the real part here, cast back into Fixed(16,8)
    fixed_outputs = [Fixed(x.real, True, 16, 8) for x in golden]
    fixed_outputs = fixed_outputs[:16]
    dut._log.info(f"Golden FFT outputs (fixed-point): {fixed_outputs}")


    # build your SPI‐packed in/out message lists
    in_msgs, out_msgs = fft1_msg([fixed_inputs], [fixed_outputs])

    # Plot the FFT inputs and outputs on separate graphs
    plot_fft_outputs_dual(fixed_inputs, fixed_outputs, title="Golden FFT vs SPI Output Messages", filename_prefix="fft_outputs_dual")

    # run the transaction‐level SPI harness
    # Note: run_top already logs the actual DUT output messages as they are received.
    await run_top(dut, in_msgs, out_msgs, max_trsns=200)


@cocotb.test()
async def test_fft1_classifier_with_wav(dut):
    """Test classifier on real-world audio input."""
    # drive clock and reset
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)

    # load & quantize the first 32 samples as Q8.8 int16
    raw_bytes = wav_to_q8_8_messages("input.wav", target_rate=48000)
    raw_bytes = raw_bytes[:32]
    fixed_inputs = [Fixed(s, True, 16, 8) for s in raw_bytes]

    # compute golden FFT output
    model = FFTPease(16, 8, 32)
    golden = model.transform([CFixed(v=(s, 0), n=16, d=8) for s in raw_bytes])
    fft_reals = [x.real for x in golden]

    # classifier parameters
    cutoff_freq = 1000
    cutoff_mag = Fixed(0.7, True, 16, 8)
    sampling_freq = 48000

    # compute expected classifier outputs
    classifier_outputs = classify(fft_reals, cutoff_freq, cutoff_mag, sampling_freq)

    # build SPI message lists for FFT1->Classifier->Arbiter pipeline
    in_msgs = [
        mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1),
        mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_CLS),
        mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.CLS_ARBITER),
        mk_spi_pkt(RouterOut.CLS_CUT_FREQ_CTRL, cutoff_freq),
        mk_spi_pkt(RouterOut.CLS_MAG_CTRL, int(cutoff_mag)),
        mk_spi_pkt(RouterOut.CLS_SAMP_FREQ_CTRL, sampling_freq),
    ] + [mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for x in fixed_inputs]

    # Classifier output is a single boolean, convert to int and wrap in a list
    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, int(classifier_outputs))]

    # run the transaction-level SPI harness with ample cycles
    await run_top(dut, in_msgs, out_msgs, max_trsns=2000)

    # log expected classifier output
    dut._log.info(f"Expected classifier output: {classifier_outputs}")


@cocotb.test()
async def test_fft1_classifier_with_ffff_cutoff_mag(dut):
    """Test classifier when cutoff is maximized. Expected output is false."""
    # drive clock and reset
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)

    # prepare 32 zero samples as Fixed(16,8)
    fixed_inputs = [Fixed(0, True, 16, 8) for _ in range(32)]
    dut._log.info(f"Zero inputs (fixed-point): {fixed_inputs}")

    # expected classifier input is zeros -> FFT output all zeros real part
    fft_reals_float = [0.0]*32
    # Convert floats to Fixed(16, 8) for the classifier
    fft_reals_fixed = [Fixed(x, True, 16, 8) for x in fft_reals_float]
    cutoff_freq = 10
    cutoff_mag  = Fixed(v=0xFFFF, signed=False, n=16, d=8)  # Set to a negative value to ensure no output
    #Fixed(0.7, True, 16, 8)
    sampling_freq = 44100

    # compute expected classifier result
    expected = classify(fft_reals_fixed, cutoff_freq, cutoff_mag, sampling_freq)

    # expect 0xFFFF = 255
    dut._log.info(f"int(cutoff_mag): {int(cutoff_mag)}")
    # build SPI packets
    in_msgs = [
        mk_spi_pkt(RouterOut.IN_XBAR_CTRL,    InXbarCfg.ROUTER_FFT1),
        mk_spi_pkt(RouterOut.CLS_XBAR_CTRL,   ClsXbarCfg.FFT1_CLS),
        mk_spi_pkt(RouterOut.OUT_XBAR_CTRL,   OutXbarCfg.CLS_ARBITER),
        mk_spi_pkt(RouterOut.CLS_CUT_FREQ_CTRL, cutoff_freq),
        mk_spi_pkt(RouterOut.CLS_MAG_CTRL,    int(cutoff_mag)),
        mk_spi_pkt(RouterOut.CLS_SAMP_FREQ_CTRL, sampling_freq),
    ] + [mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for x in fixed_inputs]

    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, int(expected))]

    await run_top(dut, in_msgs, out_msgs, max_trsns=2000)

    dut._log.info(f"Expected classifier output (zero inputs): {expected}")