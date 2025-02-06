import math
import random
import cocotb
import subprocess
from cocotb.triggers import *
from cocotb.clock import Clock

X = 'xxxxxxxxxxxxxxxx'

#====================================================================================
# SIGN_EXTEND
#====================================================================================

def SIGN_EXTEND(value, bits):
  sign_bit = (1 << (bits - 1))
  return (value & (sign_bit - 1)) - (value & sign_bit)

#====================================================================================
# SystolicMMPE
#====================================================================================

def SystolicMMPE(x, w, s):
  x_out = x
  w_out = w
  prod  = ((SIGN_EXTEND(x, 16) * SIGN_EXTEND(w, 16)) >> 8) & 0xffff
  s_out = (s + prod) & 0xffff
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
  dut.x_in.value = x_in
  dut.w_in.value = w_in
  
  await RisingEdge(dut.clk)

  assert (dut.x_out.value == x_out),             \
    "[FAILED] dut.x_out != ref.x_out ({} != {})" \
    .format(dut.x_out.value, x_out)
  assert (dut.w_out.value == w_out),             \
    "[FAILED] dut.w_out != ref.w_out ({} != {})" \
    .format(dut.w_out.value, w_out)
  assert (dut.s_out.value == s_out),             \
    "[FAILED] dut.s_out != ref.s_out ({} != {})" \
    .format(dut.s_out.value, s_out)

#====================================================================================
# test_simple
#====================================================================================

@cocotb.test()
async def test_simple(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  # 0.0 = 00000000.00000000 (Q8.8) = 0x0000
  # 1.0 = 00000001.00000000 (Q8.8) = 0x0100

  await SystolicMMPE_RESET(dut)
  
  #                                rst en  x_in    w_in    x_out   w_out   s_out
  await SystolicMMPE_CHECK_EQ( dut, 0, 1, 0x0100, 0x0000, 0x0000, 0x0000, 0x0000 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 1, 0x0100, 0x0100, 0x0100, 0x0000, 0x0000 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 1, 0x0000, 0x0000, 0x0100, 0x0100, 0x0100 )

#====================================================================================
# test_directed_enable
#====================================================================================

@cocotb.test()
async def test_directed_enable(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  # 0.0 = 00000000.00000000 (Q8.8) = 0x0000
  # 1.0 = 00000001.00000000 (Q8.8) = 0x0100
  # 2.0 = 00000010.00000000 (Q8.8) = 0x0200

  await SystolicMMPE_RESET(dut)

  #                                rst en  x_in    w_in    x_out   w_out   s_out
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, 0x0100, 0x0100, 0x0000, 0x0000, 0x0000 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 1, 0x0100, 0x0100, 0x0000, 0x0000, 0x0000 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, 0x0000, 0x0000, 0x0100, 0x0100, 0x0100 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 1, 0x0000, 0x0000, 0x0100, 0x0100, 0x0100 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, 0x0100, 0x0100, 0x0000, 0x0000, 0x0100 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 1, 0x0100, 0x0100, 0x0000, 0x0000, 0x0100 )
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, 0x0000, 0x0000, 0x0100, 0x0100, 0x0200 )

#====================================================================================
# test_random_source
#====================================================================================

@cocotb.test()
async def test_random_source(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  size = 1000000

  x = []
  w = []

  for i in range(size):
    x.append(random.randint(0,pow(2,15)))
    w.append(random.randint(0,pow(2,15)))
  
  await SystolicMMPE_RESET(dut)

  x_out = 0
  w_out = 0
  s_out = 0

  for i in range(size):
    await SystolicMMPE_CHECK_EQ( dut, 0, 1, x[i], w[i], x_out, w_out, s_out )
    x_out, w_out, s_out = SystolicMMPE(x[i], w[i], s_out)
  
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, 0, 0, x_out, w_out, s_out )

#====================================================================================
# test_random_source_enable
#====================================================================================

@cocotb.test()
async def test_random_source_enable(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  size = 1000000

  x = []
  w = []

  for i in range(size):
    x.append(random.randint(0,pow(2,15)))
    w.append(random.randint(0,pow(2,15)))
  
  await SystolicMMPE_RESET(dut)

  x_out = 0
  w_out = 0
  s_out = 0

  for i in range(size):
    en = random.randint(0, 1)
    await SystolicMMPE_CHECK_EQ( dut, 0, en, x[i], w[i], x_out, w_out, s_out )

    if en:
      x_out, w_out, s_out = SystolicMMPE(x[i], w[i], s_out)
  
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, 0, 0, x_out, w_out, s_out )

#====================================================================================
# test_random_source_enable_reset
#====================================================================================

@cocotb.test()
async def test_random_source_enable_reset(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  size = 1000000

  x = []
  w = []

  for i in range(size):
    x.append(random.randint(0,pow(2,15)))
    w.append(random.randint(0,pow(2,15)))
  
  await SystolicMMPE_RESET(dut)

  x_out = 0
  w_out = 0
  s_out = 0

  for i in range(size):
    rst = random.randint(0, 1)
    en  = random.randint(0, 1)
    await SystolicMMPE_CHECK_EQ( dut, rst, en, x[i], w[i], x_out, w_out, s_out )

    if rst:
      x_out = 0
      w_out = 0
      s_out = 0
    elif en:
      x_out, w_out, s_out = SystolicMMPE(x[i], w[i], s_out)
  
  await SystolicMMPE_CHECK_EQ( dut, 0, 0, 0, 0, x_out, w_out, s_out )