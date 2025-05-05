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

DROP_RATE = 10

raw_bytes = wav_to_q8_8_messages("input.wav", 0)
raw_bytes = raw_bytes[:len(raw_bytes)//(DROP_RATE * FFT_ARRAY_SIZE) * (DROP_RATE * FFT_ARRAY_SIZE) - 1]

dropped_bytes = drop_bytes(raw_bytes, DROP_RATE)
# resampled_bytes = resample(raw_bytes, len(raw_bytes)//DROP_RATE)

fft_outputs = []

def int_to_twos_complement(value, num_bits=NUM_BITS):
    if value < 0:
        value = (1 << num_bits) + value
    return format(value, f'0{num_bits}b')


def analyze_real_fft_output(fft_out: list, is_external: int):
    n = len(fft_out)

    freqs = np.fft.fftfreq(n, d=1/(96000/DROP_RATE))
    magnitudes = []
    
    for c in fft_out:
        real = c.real.get(True) / (1 << 8)
        imag = c.imag.get(True) / (1 << 8)
        mag = (real**2 + imag**2)**0.5
        magnitudes.append(real)

    plt.figure(figsize=(10, 5))
    plt.plot(freqs[:n//2], magnitudes[:n//2])
    plt.title("FFT Magnitude Spectrum")
    plt.xlabel("Frequency (Hz)")
    plt.ylabel("Magnitude")
    plt.grid(True)
    if(is_external == 1):
        plt.savefig(f"figures/external_bins{DROP_RATE}.png")
    else:
        plt.savefig(f"figures/bins{DROP_RATE}.png")


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
            av.binstr = int_to_twos_complement(dropped_bytes[i//DROP_RATE])
            assert dut.drop_unit.resp_msg.value == av
        if dut.resp_val.value == 1:
            fft_outputs.append(CFixed(v=(dut.resp_msg.value.integer, 0), n=NUM_BITS, d=8, raw=True))

    analyze_real_fft_output(fft_outputs[0:16], 0)

# model = FFTPease(16, 8, 32)
# golden = model.transform([CFixed(v=(s, 0), n=16, d=8) for s in resampled_bytes[:32]])
# fixed_outputs = [Fixed(x.real, True, 16, 8) for x in golden]
# analyze_real_fft_output(golden[0:16], 1)
