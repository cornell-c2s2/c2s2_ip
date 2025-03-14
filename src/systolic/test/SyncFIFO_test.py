import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

depth = 16
nbits = 16

async def reset(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)
  dut.rst.value = 0

async def rw_ptr_step(dut, wen, ren, full, empty):
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

#===========================================================
# test_case_1_simple_rw_ptr_step
#===========================================================

@cocotb.test()
async def test_case_1_simple_rw_ptr_step(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  for T in range(10000):
    #                      wen ren full empty
    await rw_ptr_step(dut, 1,  0,  0,    1  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  1,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )

#===========================================================
# test_case_2_random_rw_ptr_step
#===========================================================

@cocotb.test()
async def test_case_2_random_rw_ptr_step(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  full       = 0
  empty      = 1
  curr_depth = 0

  for T in range(10000):
    wen = random.randint(0, 1)
    ren = random.randint(0, 1)

    await rw_ptr_step(dut, wen, ren, full, empty)

    curr_depth += int(wen & (wen ^ full)) - int(ren & (ren ^ empty))

    full  = int(curr_depth == depth)
    empty = int(curr_depth == 0)