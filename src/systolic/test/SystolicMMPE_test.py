import cocotb
import subprocess
from cocotb.triggers import *
from cocotb.clock import Clock

X = 'xxxxxxxxxxxxxxxx'

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
# SystolicMMPE_RESET
#====================================================================================

async def SystolicMMPE_RESET(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)

#====================================================================================
# test_simple
#====================================================================================

@cocotb.test()
async def test_simple(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())

  # 1.0 = 00000001.00000000 (Q8.8) = 0x0100
  # 0.0 = 00000000.00000000 (Q8.8) = 0x0000

  x = [0x0100, 0x0100]
  w = [0x0000, 0x0100]

  size = 2

  await SystolicMMPE_RESET(dut)

  x_out = 0
  w_out = 0
  s_out = 0

  for i in range(size):
    await SystolicMMPE_CHECK_EQ( dut, 0, 1, x[i], w[i], x_out, w_out, s_out )

    x_out  = x[i]
    w_out  = w[i]
    s_out += (x[i] * w[i]) >> 8
  
  await SystolicMMPE_CHECK_EQ( dut, 0, 1, 0, 0, x_out, w_out, s_out )