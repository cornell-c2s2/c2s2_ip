import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

size  = 16
nbits = 16
dbits = 8

#===========================================================

def rand_fp(n, d):
    return Fixed(random.randint(0, (1 << n) - 1), 1, n, d, raw=True)

#===========================================================

async def reset(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)
  dut.rst.value = 0

async def step(dut, d, sel, wen, ren, full, empty, out):
  dut.d.value = d
  dut.sel.value = sel

  for i in range(size):
    dut.wen[i].value = wen[i]
    dut.ren[i].value = ren[i]
  
  await RisingEdge(dut.clk)

  for i in range(size):
    assert (dut.full[i].value == full[i])
    assert (dut.empty[i].value == empty[i])
    assert (dut.out[i].value == out[i])

#===========================================================

@cocotb.test()
async def test_case_1_directed_x_buffer(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # sel:   [0] [1] [2] [3] [4] [5] [6] [7] [8] [9] [A] [B] [C] [D] [E] [F]
  wen   = [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ]
  ren   = [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ]
  full  = [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ]
  empty = [ 1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1 ]
  out   = [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ]
  _out  = [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ]

  # simulate tensor buffer write-data flow

  for sel in range(size):
    wen[sel] = 1
    for d in range(size):
      await step(dut, d, sel, wen, ren, full, empty, out)
      full[sel]  = (d == size-1)
      empty[sel] = 0
    wen[sel] = 0
    await step(dut, d, sel, wen, ren, full, empty, out)
  
  # simulate tensor buffer read-data flow

  for sel in range(size):
    ren[sel] = 1
    await step(dut, d, sel, wen, ren, full, empty, out)
    for i in range(sel+1):
      full[i]  = 0
      empty[i] = (_out[i] >= size-1)
      _out[i] += 1

      if empty[i]:
        out[i] = 0
      else:
        out[i] = _out[i]

  for t in range(size):
    await step(dut, d, sel, wen, ren, full, empty, out)
    for i in range(size):
      full[i]  = 0
      empty[i] = (_out[i] >= size-1)
      _out[i] += 1

      if empty[i]:
        out[i] = 0
      else:
        out[i] = _out[i]

  await step(dut, d, sel, wen, ren, full, empty, out)