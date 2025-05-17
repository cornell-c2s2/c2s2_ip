import math
import random
import cocotb
import subprocess
import numpy as np
from cocotb.triggers import *
from cocotb.clock import Clock

from fixedpt import Fixed

LOW = Fixed(0, 1, 16, 8)

def random_fp_16b():
  int_8b = np.random.randint(-2**7, 2**7)    # [-128, 127]
  dec_8b = np.random.randint(0, 2**8) / 2**8 # [0, 0.996]
  return int_8b + dec_8b

#====================================================================================
# fixed_point_multiply
#====================================================================================

def fixed_point_multiply(a: Fixed, b: Fixed) -> Fixed:
    assert a._n == b._n
    assert a._d == b._d
    return (a * b).resize(None, a._n, a._d)

#====================================================================================
# SystolicMMPE
#====================================================================================

def SystolicMMPE(x, w, s):
  x_out = Fixed(x, 1, 16, 8)
  w_out = Fixed(w, 1, 16, 8)
  prod  = fixed_point_multiply(x, w)
  s_out = Fixed(s + prod, 1, 16, 8)
  return x_out, w_out, s_out

#====================================================================================
# SystolicMMPE_RESET
#====================================================================================

async def SystolicMMPE_RESET(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)

#====================================================================================
# SystolicMMPE_CHECK_EQ
#====================================================================================

async def SystolicMMPE_CHECK_EQ(dut, rst, en, x_in, w_in, x_out, w_out, s_out):
  dut.rst.value  = rst
  dut.en.value   = en
  dut.x_in.value = x_in.get()
  dut.w_in.value = w_in.get()
  
  await RisingEdge(dut.clk)

  assert (dut.x_out.value == x_out.get()),       \
    "[FAILED] dut.x_out != ref.x_out ({} != {})" \
    .format(dut.x_out.value, x_out.get())
  assert (dut.w_out.value == w_out.get()),       \
    "[FAILED] dut.w_out != ref.w_out ({} != {})" \
    .format(dut.w_out.value, w_out.get())
  assert (dut.s_out.value == s_out.get()),       \
    "[FAILED] dut.s_out != ref.s_out ({} != {})" \
    .format(dut.s_out.value, s_out.get())

#====================================================================================
# test_random_source
#====================================================================================

@cocotb.test()
async def test_random_source(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  size = 10000

  x = []
  w = []

  for i in range(size):
    x.append(Fixed(random_fp_16b(), 1, 16, 8))
    w.append(Fixed(random_fp_16b(), 1, 16, 8))
  
  await SystolicMMPE_RESET(dut)

  x_out = LOW
  w_out = LOW
  s_out = LOW

  for i in range(size):
    await SystolicMMPE_CHECK_EQ( dut, 0, 1, x[i], w[i], x_out, w_out, s_out )
    x_out, w_out, s_out = SystolicMMPE(x[i], w[i], s_out)
  
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, LOW, LOW, x_out, w_out, s_out )

#====================================================================================
# test_random_source_enable
#====================================================================================

@cocotb.test()
async def test_random_source_enable(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  size = 10000

  x = []
  w = []

  for i in range(size):
    x.append(Fixed(random_fp_16b(), 1, 16, 8))
    w.append(Fixed(random_fp_16b(), 1, 16, 8))
  
  await SystolicMMPE_RESET(dut)

  x_out = LOW
  w_out = LOW
  s_out = LOW

  for i in range(size):
    en = random.randint(0, 1)
    await SystolicMMPE_CHECK_EQ( dut, 0, en, x[i], w[i], x_out, w_out, s_out )

    if en:
      x_out, w_out, s_out = SystolicMMPE(x[i], w[i], s_out)
  
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, LOW, LOW, x_out, w_out, s_out )

#====================================================================================
# test_random_source_enable_reset
#====================================================================================

@cocotb.test()
async def test_random_source_enable_reset(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  size = 10000

  x = []
  w = []

  for i in range(size):
    x.append(Fixed(random_fp_16b(), 1, 16, 8))
    w.append(Fixed(random_fp_16b(), 1, 16, 8))
  
  await SystolicMMPE_RESET(dut)

  x_out = LOW
  w_out = LOW
  s_out = LOW

  for i in range(size):
    rst = random.randint(0, 1)
    en  = random.randint(0, 1)
    await SystolicMMPE_CHECK_EQ( dut, rst, en, x[i], w[i], x_out, w_out, s_out )

    if rst:
      x_out = LOW
      w_out = LOW
      s_out = LOW
    elif en:
      x_out, w_out, s_out = SystolicMMPE(x[i], w[i], s_out)
  
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, LOW, LOW, x_out, w_out, s_out )