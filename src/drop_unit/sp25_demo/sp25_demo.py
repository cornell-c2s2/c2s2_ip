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
DECIMAL_BITS = 8
FFT_ARRAY_SIZE = 64

DROP_RATE = 10
ENABLE = 0

raw_bytes = wav_to_q8_8_messages("input.wav", 0)
raw_bytes = raw_bytes[:len(raw_bytes)//(DROP_RATE * FFT_ARRAY_SIZE * 8) * (DROP_RATE * FFT_ARRAY_SIZE) - 1]

dropped_bytes = drop_bytes(raw_bytes, DROP_RATE)
if ENABLE == 0:
    resampled_bytes = resample(raw_bytes, len(raw_bytes)//DROP_RATE)
else:
    resampled_bytes = resample(raw_bytes, len(raw_bytes))

fft_outputs = []

def int_to_twos_complement(value, num_bits=NUM_BITS):
    if value < 0:
        value = (1 << num_bits) + value
    return format(value, f'0{num_bits}b')


def analyze_real_fft_output(fft_out: list, is_external: int):
    n = len(fft_out)
    if ENABLE == 0:
        d = 1/(96000/DROP_RATE)
    else:
        d = 1/96000

    freqs = np.fft.fftfreq(n, d=d)
    magnitudes = []
    
    for c in fft_out:
        real = c.real.get(True) / (1 << DECIMAL_BITS)
        # imag = c.imag.get(True) / (1 << 8)
        # mag = (real**2 + imag**2)**0.5
        magnitudes.append(real)

    plt.figure(figsize=(10, 5))
    plt.plot(freqs[:n//2], magnitudes[:n//2])
    plt.title("FFT Magnitude Spectrum")
    plt.xlabel("Frequency (Hz)")
    plt.ylabel("Magnitude")
    plt.grid(True)
    if ENABLE == 0:
        if(is_external == 1):
            plt.savefig(f"figures/external_bins{DROP_RATE}.png")
        else:
            plt.savefig(f"figures/bins{DROP_RATE}.png")
    else:
        if(is_external == 1):
            plt.savefig(f"figures/bins_external_enable.png")
        else:
            plt.savefig(f"figures/bins_enable.png")


@cocotb.test()
async def demo_check_drop(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    dut.reset.value = 1
    dut.enable.value = ENABLE
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
            if ENABLE == 0:
                av.binstr = int_to_twos_complement(dropped_bytes[i//DROP_RATE])
            else:
                av.binstr = int_to_twos_complement(raw_bytes[i])
            assert dut.drop_unit.resp_msg.value == av
        if dut.resp_val.value == 1:
            fft_outputs.append(CFixed(v=(dut.resp_msg.value.integer, 0), n=NUM_BITS, d=DECIMAL_BITS, raw=True))

    analyze_real_fft_output(fft_outputs[0:FFT_ARRAY_SIZE//2], 0)

    model = FFTPease(NUM_BITS, DECIMAL_BITS, FFT_ARRAY_SIZE)
    golden = model.transform([CFixed(v=(s, 0), n=NUM_BITS, d=DECIMAL_BITS) for s in resampled_bytes[:FFT_ARRAY_SIZE]])
    analyze_real_fft_output(golden[0:FFT_ARRAY_SIZE//2], 1)
    