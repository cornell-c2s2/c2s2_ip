import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

size = 4

LOAD = 0b001
MAC  = 0b010
OUT  = 0b100

#===========================================================

async def d2c(dut, x_send_val, w_send_val, x_fifo_full, x_fifo_empty, w_fifo_full, w_fifo_empty):
  dut.x_send_val.value = x_send_val
  dut.w_send_val.value = w_send_val
  
  for i in range(size):
    dut.x_fifo_full[i].value  = x_fifo_full[i]
    dut.x_fifo_empty[i].value = x_fifo_empty[i]
    dut.w_fifo_full[i].value  = w_fifo_full[i]
    dut.w_fifo_empty[i].value = w_fifo_empty[i]

async def always_comb(dut, mac_en, x_send_rdy, w_send_rdy, x_fifo_wen, w_fifo_wen):
  await Timer(1, units="ns")
  assert (dut.mac_en.value == mac_en)
  assert (dut.x_send_rdy.value == x_send_rdy)
  assert (dut.w_send_rdy.value == w_send_rdy)
  for i in range(size):
    assert (dut.x_fifo_wen[i].value == x_fifo_wen[i])
    assert (dut.w_fifo_wen[i].value == w_fifo_wen[i])

async def always_ff(dut, state, x_fifo_ren, w_fifo_ren):
  await RisingEdge(dut.clk)
  assert (dut.trace_state.value == state)
  for i in range(size):
    assert (dut.x_fifo_ren[i].value == x_fifo_ren[i])
    assert (dut.w_fifo_ren[i].value == w_fifo_ren[i])

async def reset(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)
  dut.rst.value = 0

#===========================================================

@cocotb.test()
async def test_case_1_directed_fsm(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # @ LOAD: FIFOs are initially empty
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ LOAD: Deserializer is full (write FIFOs)
  await d2c(dut, 1, 1, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 1, [1,1,1,1], [1,1,1,1])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ LOAD: FIFOs are neither empty nor full
  await d2c(dut, 0, 0, [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ LOAD: Deserializer is full (write FIFOs)
  await d2c(dut, 1, 1, [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0])
  await always_comb(dut, 0, 1, 1, [1,1,1,1], [1,1,1,1])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ LOAD: FIFOs are full
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ MAC: FIFOs are read-enabled one at a time
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,0,0,0], [1,0,0,0])

  await d2c(dut, 0, 0, [0,1,1,1], [0,0,0,0], [0,1,1,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,0,0], [1,1,0,0])

  await d2c(dut, 0, 0, [0,0,1,1], [0,0,0,0], [0,0,1,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,0], [1,1,1,0])

  await d2c(dut, 0, 0, [0,0,0,1], [0,0,0,0], [0,0,0,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # @ MAC: FIFOs start to empty
  await d2c(dut, 0, 0, [0,0,0,0], [1,0,0,0], [0,0,0,0], [1,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,0,0], [0,0,0,0], [1,1,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,0], [0,0,0,0], [1,1,1,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # @ MAC: All FIFOs are empty
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # @ OUT
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, OUT, [0,0,0,0], [0,0,0,0])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, OUT, [0,0,0,0], [0,0,0,0])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, OUT, [0,0,0,0], [0,0,0,0])

@cocotb.test()
async def test_case_2_directed_fsm(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # @ LOAD: FIFOs are initially empty
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ LOAD: Tensor deserializer is full (write FIFOs)
  await d2c(dut, 1, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 0, [1,1,1,1], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ LOAD: Weight deserializer is full (write FIFOs)
  await d2c(dut, 0, 1, [0,0,0,0], [0,0,0,0], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 0, 1, [0,0,0,0], [1,1,1,1])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ LOAD: FIFOs are neither empty nor full
  await d2c(dut, 0, 0, [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  #
  # ...
  #

  # @ LOAD: Tensor FIFOs are full
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [0,0,0,0], [0,0,0,0])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  #
  # ...
  #

  # @ LOAD: Weight FIFOs are full
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # @ MAC: FIFOs are read-enabled one at a time
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,0,0,0], [1,0,0,0])

  await d2c(dut, 0, 0, [0,1,1,1], [0,0,0,0], [0,1,1,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,0,0], [1,1,0,0])

  await d2c(dut, 0, 0, [0,0,1,1], [0,0,0,0], [0,0,1,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,0], [1,1,1,0])

  await d2c(dut, 0, 0, [0,0,0,1], [0,0,0,0], [0,0,0,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # @ MAC: FIFOs start to empty
  await d2c(dut, 0, 0, [0,0,0,0], [1,0,0,0], [0,0,0,0], [1,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,0,0], [0,0,0,0], [1,1,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,0], [0,0,0,0], [1,1,1,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # @ MAC: All FIFOs are empty
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # @ OUT
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, OUT, [0,0,0,0], [0,0,0,0])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, OUT, [0,0,0,0], [0,0,0,0])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, OUT, [0,0,0,0], [0,0,0,0])