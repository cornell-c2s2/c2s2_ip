import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import *

@cocotb.test()
async def test(dut):
  clock = Clock(dut.clk, 10, units="ns")
  cocotb.start_soon(clock.start(start_high=False))
  await RisingEdge(dut.clk)