# Cocotb imports
import cocotb
import os
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb.runner import get_runner

# Util imports
import random

# Use environment variables for model parameters set in the Makefile as a reference for writing tests
# Examples (from multiplier example):
# bits = int(os.getenv("N", 32))
# decimal = int(os.getenv("D", 16))

# Generate clock pulses
async def generate_clock(dut, cycles):
    for cycle in range(cycles):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

# Use this as reference for creating tests. Make sure to run this test with only "pass" to see if your 
# your envoronment is properly configured.
@cocotb.test()
async def sample_test(dut):
    pass
