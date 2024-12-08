# Imports needed by cocotb
import pytest
import os
import random
import sys
import subprocess
from pathlib import Path
import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.binary import BinaryValue
import pdb
from lfsr_model import *

# Helper tasks -------------------------------------------------------------
#Generate clock pulses
async def generate_clock(dut):
    while(1):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")


# # dut: dut instance
# # seed: initial seed to test
# # num_test_patterns: the number of test vectors to generate
# async def lfsr_simple_test(dut, seed, num_test_vectors):
#     # Reset
#     dut.reset.value = 1

#     #Start clock
#     await ClockCycles(dut.clk, 1)

#     # Reset to 0
#     dut.reset.value = 0
#     await ClockCycles(dut.clk, 1)
#     await ClockCycles(dut.clk, 1)

#     # Send in a valid seed
#     dut.req_val = 1
#     dut.req_msg = seed
#     await ClockCycles(dut.clk, 1)

#     dut.req_val = 0

#     for i in range(num_test_vectors):
#         dut.resp_val = 1
#         dut._log.info(f"LFSR TEST VECTOR: {dut.resp_msg}")
#         dut._log.info(f"LFSR STATE: {dut.state}")
#         await ClockCycles(dut.clk, 1)
    
#     # Consumer no longer wants a test vector
#     dut.resp_val = 0


# dut: dut instance
# seed: initial seed to test
# num_test_patterns: the number of test vectors to generate
async def lfsr_simple_test(dut, seed, num_test_vectors):
    # Start the clock
    # cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    # Reset
    dut.reset.value = 1
    await RisingEdge(dut.clk)


    # Reset to 0
    dut.reset.value = 0
    await RisingEdge(dut.clk)

    # Send in a valid seed
    dut.req_val = 1
    dut.req_msg = seed
    await RisingEdge(dut.clk)

    dut.req_val = 0

    for i in range(num_test_vectors):
        dut.resp_rdy = 1
        dut._log.info(f"LFSR TEST VECTOR: {dut.resp_msg}")
        # dut._log.info(f"LFSR STATE: {dut.state}")
        await RisingEdge(dut.clk)
    
    # Consumer no longer wants a test vector
    dut.resp_rdy = 0

    # Ensure the LFSR is paused
    dut._log.info("CONSTANT")
    await RisingEdge(dut.clk)
    dut._log.info(f"LFSR TEST VECTOR: {dut.resp_msg}")
    dut._log.info(f"LFSR STATE: {dut.state}")

    await RisingEdge(dut.clk)
    dut._log.info(f"LFSR TEST VECTOR: {dut.resp_msg}")
    dut._log.info(f"LFSR STATE: {dut.state}")




# @cocotb.test()
async def lfsr_test1(dut):
    await cocotb.start(generate_clock(dut))
    # Test Variables
    num_test_vectors = 3
    # 3982994221 == 32'b11101101011001111010101100101101
    seed = 3982994221
    await lfsr_simple_test(dut, seed, num_test_vectors)


@cocotb.test()
async def lfsr_test2(dut):
    await cocotb.start(generate_clock(dut))
    # Test Variables
    num_test_vectors = 3
    # 2268756060 == 32'b10000111001110100111100001011100
    seed = 2268756060
    await lfsr_simple_test(dut, seed, num_test_vectors)
    
