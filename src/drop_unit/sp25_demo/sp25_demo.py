import random
import os
import sys

current_dir = os.path.dirname(__file__)
src_root = os.path.abspath(os.path.join(current_dir, "../../../"))
sys.path.insert(0, src_root)

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from dropunit_sim import wav_to_q8_8_messages, drop_bytes
from src.fft.pease.sim import fft
from fixedpt import CFixed
from cocotb.binary import BinaryValue

# parameters
NUM_BITS = 16
FFT_ARRAY_SIZE = 32

DROP_RATE = 10

raw_bytes = wav_to_q8_8_messages("input.wav", 0)
raw_bytes = raw_bytes[:len(raw_bytes)//(DROP_RATE * FFT_ARRAY_SIZE) * (DROP_RATE * FFT_ARRAY_SIZE) - 1]

downsampled_bytes = drop_bytes(raw_bytes, DROP_RATE)

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
        v.signed_integer = raw_bytes[i]
        if raw_bytes[i]:
            dut.req_msg.value = v
        else:
            dut.req_msg.value = 0
        dut.req_val.value = 1
        await ClockCycles(dut.clk, 1)
        
        if dut.drop_unit.resp_val.value == 1:
            av = BinaryValue(n_bits=NUM_BITS, binaryRepresentation=2)
            av.signed_integer = downsampled_bytes[i//DROP_RATE]
            if downsampled_bytes[i//DROP_RATE]:
                assert dut.drop_unit.resp_msg.value == av
            else:
                assert dut.drop_unit.resp_msg.value == 0
        
    await ClockCycles(dut.clk, FFT_ARRAY_SIZE)
