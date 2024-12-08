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

# Global Params ------------------------------------------------------------
NUM_RANDOM_TESTS = 5
TB_SEED = 0

# Helper tasks -------------------------------------------------------------
async def lbist_top_simple(dut):
    # Reset
    dut.reset.value = 1

    #Start clock
    await ClockCycles(dut.clk, 1)

    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    dut.lbist_req_val.value = 1
    await ClockCycles(dut.clk, 1)

    while dut.lbist_resp_val.value != 1:
        await ClockCycles(dut.clk, 1)

    dut._log.info(f"TEST OUTPUT: {dut.lbist_resp_msg.value}")





# Tests --------------------------------------------------------------------
# Single directed test
@cocotb.test()
async def lbist_top_test1(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    await lbist_top_simple(dut)

