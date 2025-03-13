import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

async def reset(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)
  dut.rst.value = 0

async def read_write_en_step(dut, wen, ren, full, empty):
  dut.rst.value = 0
  dut.wen.value = wen
  dut.ren.value = ren

  await RisingEdge(dut.clk)

  assert (dut.full.value == full),             \
    "FAILED: dut.full ({}) != ref.full ({})"   \
    .format(dut.full.value, full)
  assert (dut.empty.value == empty),           \
    "FAILED: dut.empty ({}) != ref.empty ({})" \
    .format(dut.empty.value, empty)

@cocotb.test()
async def test_case_1_pointers(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  #                            wen ren full empty
  await read_write_en_step(dut, 1,  0,  0,    1  )
  await read_write_en_step(dut, 1,  0,  0,    0  )
  await read_write_en_step(dut, 1,  0,  0,    0  )
  await read_write_en_step(dut, 1,  0,  0,    0  )
  await read_write_en_step(dut, 0,  0,  1,    0  )