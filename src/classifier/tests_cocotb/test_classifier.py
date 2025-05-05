import random
import math
import pdb
import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
import pdb
from classifier_model import *
from cocotb.regression import TestFactory


async def test_classifier(dut, cutoff_freq, cutoff_mag, sampling_freq):
    random.seed("C2S2")
    recv_msg = [0] * dut.N_SAMPLES.value
    for i in range(dut.N_SAMPLES.value):
        recv_msg[i] = random.randint(1, 60)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    dut._log.info(f"DUT parameters (BIT_WIDTH): {dut.BIT_WIDTH.value}")
    dut._log.info(f"DUT parameters (FREQ_BIT_WIDTH): {dut.FREQ_BIT_WIDTH.value}")
    dut._log.info(f"DUT parameters (N_SAMPLES): {dut.N_SAMPLES.value}")

    params = [dut.BIT_WIDTH.value, dut.FREQ_BIT_WIDTH.value, dut.N_SAMPLES.value]
    model_output = classify(cutoff_freq, cutoff_mag, sampling_freq, recv_msg, params)
    send_msg = model_output[0]

    await ClockCycles(dut.clk, 1)

    # Reset to 1
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    
    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    # Set the cutoff freq
    dut.cutoff_freq_val.value = 1
    dut.cutoff_freq_msg.value = cutoff_freq

    # Set the cutoff mag
    dut.cutoff_mag_val.value = 1
    dut.cutoff_mag_msg.value = cutoff_mag

    # Set the sampling freq
    dut.sampling_freq_val.value = 1
    dut.sampling_freq_msg.value = sampling_freq

    await ClockCycles(dut.clk, 1)

    # Ex: Assuming FFT has sampling freq of 40KHz. This means bin resolution is
    # 40000/32 = 1250 Hz 
    # | Bin Index | Frequency (Hz)   |
    # | --------- | ---------------- |
    # | 0         | 0                |
    # | 1         | 1,250            |
    # | 2         | 2,500            |
    # | 3         | 3,750            |
    # | 4         | 5,000            |
    # | 5         | 6,250            |
    # | 6         | 7,500            |
    # | 7         | 8,750            |
    # | 8         | 10,000           |
    # | 9         | 11,250           |
    # | 10        | 12,500           |
    # | 11        | 13,750           |
    # | 12        | 15,000           |
    # | 13        | 16,250           |
    # | 14        | 17,500           |
    # | 15        | 18,750           |
    # | 16        | 20,000 (Nyquist) |


    dut.recv_msg.value = recv_msg
    dut.recv_val.value = 1

    await ClockCycles(dut.clk, 1)

    dut._log.info("==================================================")
    dut._log.info("----")

    if(send_msg != dut.send_msg.value):
        dut._log.info("==================================================")
        dut._log.info("Frequency bins")
        for idx,freq in enumerate(dut.frequency_array.value):
            dut._log.info(f"Bin Index: {idx}, Frequency Valid: {dut.out_filter.value[idx]}, Frequency Value: {int(freq)}")

        dut._log.info("==================================================")
        dut._log.info(f"Cutoff Magnitude: {int(dut.in_cutoff_mag.value)}")
        dut._log.info(f"Cutoff freq: {int(dut.in_cutoff_freq.value)}")
        dut._log.info(f"Actual")
        for idx,bin in enumerate(dut.comparison.mag_in.value):
            dut._log.info(f"ACTUAL  : Bin Index: {idx}, Bin Freq Valid: {dut.comparison.filtered_valid.value[idx]}, Bin Cutoff mag met: {dut.comparison.magnitude_val.value[idx]}, Bin Valid: {dut.comparison.compare_outs.value[dut.N_SAMPLES.value - 1 - idx]}, Bin Value: {int(bin)}")
            dut._log.info(f"EXPECTED: Bin Index: {idx}, Bin Freq Valid: {model_output[1][idx]}, Bin Cutoff mag met: {model_output[2][idx]}, Bin Valid: {model_output[3][idx]}, Bin Value: {int(bin)}")

        # pdb.set_trace()

        assert send_msg == dut.send_msg.value, "DUT and model outputs do not match"


cutoff_freq_values = [0, 2000, 4000, 10000, 12000]
cutoff_mag_values = [0.4, 3, 4, 7, 10, 20, 21]
cutoff_mag_values = [0x0080, 0x0300, 0x0400, 0x0700, 0x10, 20, 21]
sampling_freq_values = [44800, 44100, 25000, 8000]

factory = TestFactory(test_classifier)
factory.add_option("cutoff_freq", cutoff_freq_values)
factory.add_option("cutoff_mag", cutoff_mag_values)
factory.add_option("sampling_freq", sampling_freq_values)
factory.generate_tests()
 
 