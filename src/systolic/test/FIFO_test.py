import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

size  = 3
nbits = 16

async def reset(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)
  dut.rst.value = 0

#===========================================================
# test_case_1_pointers
#===========================================================

@cocotb.test()
async def test_case_1_pointers(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  dut.wen.value = 0
  dut.ren.value = 0
  await RisingEdge(dut.clk)
  assert (dut.full.value == 0)
  assert (dut.empty.value == 1)