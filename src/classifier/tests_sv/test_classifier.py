import random
import math

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

import pdb


CUTOFF_FREQ = 0
CUTOFF_MAG = 0xfffe
SAMP_FREQ = 44100


@cocotb.test()
async def basic_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    dut._log.info(f"DUT parameters (BIT_WIDTH): {dut.BIT_WIDTH.value}")
    dut._log.info(f"DUT parameters (DECIMAL_PT): {dut.DECIMAL_PT.value}")
    dut._log.info(f"DUT parameters (FREQ_BIT_WIDTH): {dut.FREQ_BIT_WIDTH.value}")
    dut._log.info(f"DUT parameters (N_SAMPLES): {dut.N_SAMPLES.value}")

    await ClockCycles(dut.clk, 1)

    # Reset to 1
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    
    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    # Set the cutoff freq
    # High-pass threshold: bins below this frequency are rejected
    # Unsigned
    # NON-inclusive (i.e. cutoff = 0 does not include bin 0 (bc it is always 0Hz))
    # Issue: bin zero always not valid.
    # Aside from that, this works!
    dut.cutoff_freq_val.value = 1
    dut.cutoff_freq_msg.value = CUTOFF_FREQ

    # Set the cutoff mag
    # Unsigned
    # Magnitude threshold: bins below this are rejected
    # NOT INCLUSIVE (i.e. if cutoff = 19 and bin has amplitude 19 it wont be valid)
    dut.cutoff_mag_val.value = 1
    dut.cutoff_mag_msg.value = CUTOFF_MAG

    # Set the sampling freq
    # Used to convert bin index to real frequency
    dut.sampling_freq_val.value = 1
    dut.sampling_freq_msg.value = SAMP_FREQ

    await ClockCycles(dut.clk, 1)

    # Assuming FFT has sampling freq of 40KHz. This means bin resolution is
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

    # Issue: **CLASSIFIER SEEMS TO BE MISSING BIN 16!!!**
    # fixed_point_values = [
    #     -5769,   # -22.53515625
    #     10233,   # 39.97265625
    #     11166,   # 43.6171875
    #     18386,   # 71.8203125
    #     10491,   # 40.98046875
    #     4736,    # 18.5
    #     1623,    # 6.3359375
    #     3663,    # 14.30859375
    #     1818,    # 7.1015625
    #     535,     # 2.08984375
    #     1145,    # 4.47265625
    #     1423,    # 5.55859375
    #     307,     # 1.19921875
    #     677,     # 2.64453125
    #     662,     # 2.5859375
    #     539      # 2.10546875
    # ]

    # test =[
    #     0xfc33,
    #     0x01e2,
    #     0xff7c,
    #     0x0026,
    #     0x006d,
    #     0x000c,
    #     0xffc6,
    #     0xffc4,
    #     0x001e,
    #     0xfff6,
    #     0xffda,
    #     0xff71,
    #     0x0013,
    #     0x001a,
    #     0x003c,
    #     0x0042]
    test = [0 for _ in range(16)]
    test[3] = 0xffff

    bv = 0
    word_width = 16

    for val in test:
        dut._log.info(f"val: {hex(val)}")
        masked_val = val & 0xFFFF
        dut._log.info(f"masked val: {hex(masked_val)}")
        dut._log.info(f"bv: {bv}")
        bv = bv << word_width
        dut._log.info(f"shifted bv: {bv}")
        bv = bv | masked_val
        dut._log.info(f"masked bv: {bv}")


        
    
    from cocotb.binary import BinaryValue
    classifier_input = BinaryValue(value=bv, n_bits=16*len(test), bigEndian=False)

    classifier_input = test
    
    # for bin_idx in range(dut.N_SAMPLES.value):
    #     if bin_idx == 0:
    #         classifier_input.append(1)
    #     else:
    #         classifier_input.append(0x0100)

    dut.recv_msg.value = classifier_input
    dut.recv_val.value = 1

    await ClockCycles(dut.clk, 1)

    dut._log.info("==================================================")
    dut._log.info("recv_msg")
    for idx,bin in enumerate(dut.recv_msg.value):
        dut._log.info(f"Bin Index: {idx}, Bin Value: {bin}")

    dut._log.info("==================================================")
    dut._log.info("out_mag")
    # Magnitude module works!
    for idx,bin in enumerate(dut.out_mag.value):
        dut._log.info(f"Bin Index: {idx}, Bin Value: {bin}")

    dut._log.info("==================================================")
    dut._log.info("Frequency bins")
    for idx,freq in enumerate(dut.frequency_array.value):
        dut._log.info(f"Bin Index: {idx}, Frequency Valid: {dut.out_filter.value[idx]}, Frequency Value: {int(freq)}")

    await ClockCycles(dut.clk, 1)

    dut._log.info("==================================================")
    # comparison.v checks if the frequency bin is valid and if the amplitude is greater than the cutoff mag. 
    # Issue:
    # OLD CODE:
    #   generate
    #     for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
    #       assign magnitude_val[i] = (mag_in[i] > cutoff_mag);
    #       assign compare_outs[i] = filtered_valid[i] & magnitude_val[i];
    #     end
    #   endgenerate

    # FIXED CODE:
    #   generate
    #     for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
    #       assign magnitude_val[i] = (mag_in[N_SAMPLES - 1 - i] > cutoff_mag);
    #       assign compare_outs[i] = filtered_valid[N_SAMPLES - 1 - i] & magnitude_val[i];
    #     end
    #   endgenerate
    dut._log.info("----")
    dut._log.info(f"Cutoff Magnitude: {int(dut.in_cutoff_mag.value)}")
    for idx,bin in enumerate(dut.comparison.mag_in.value):
        dut._log.info(f"Bin Index: {idx}, Bin Freq Valid: {dut.comparison.filtered_valid.value[idx]}, Bin Cutoff mag met: {dut.comparison.magnitude_val.value[idx]}, Bin Valid: {dut.comparison.compare_outs.value[idx]}, Bin Value: {int(bin)}")
    # dut._log.info(dut.comparison.compare_outs.value)
    
    assert True

 
 