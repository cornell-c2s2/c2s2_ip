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

async def d2c(dut, x_recv_val, w_recv_val, x_fifo_full:[], x_fifo_empty:[], w_fifo_full:[], w_fifo_empty:[]):
  dut.rst.value = 0
  dut.x_recv_val.value = x_recv_val
  dut.w_recv_val.value = w_recv_val

  for i in range(size):
    dut.x_fifo_full[i].value = x_fifo_full[i]
    dut.w_fifo_full[i].value = w_fifo_full[i]
  
  for i in range(size):
    dut.x_fifo_empty[i].value = x_fifo_empty[i]
    dut.w_fifo_empty[i].value = w_fifo_empty[i]

async def always_comb(dut, mac_en, x_recv_rdy, w_recv_rdy, x_fifo_wen:[], w_fifo_wen:[]):
  dut.rst.value = 0
  await Timer(1, units="ns")
  assert (dut.mac_en.value == mac_en)
  assert (dut.x_recv_rdy.value == x_recv_rdy)
  assert (dut.w_recv_rdy.value == w_recv_rdy)
  for i in range(size):
    assert (dut.x_fifo_wen[i].value == x_fifo_wen[i])
    assert (dut.w_fifo_wen[i].value == w_fifo_wen[i])

async def always_ff(dut, state, x_fifo_ren:[], w_fifo_ren:[]):
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
async def test_reset(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 1, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 1, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

@cocotb.test()
async def test_load_x(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # x_recv_val=0, x_fifo_full=[0,0,0,0] (x_recv_rdy=1, x_fifo_wen:[0,0,0,0])
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 1, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # x_recv_val=1, x_fifo_full=[0,0,0,0] (x_recv_rdy=1, x_fifo_wen:[1,1,1,1])
  await d2c(dut, 1, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 1, [1,1,1,1], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # x_recv_val=0, x_fifo_full=[1,1,1,1] (x_recv_rdy=0, x_fifo_wen:[0,0,0,0])
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 0, 1, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # x_recv_val=1, x_fifo_full=[1,1,1,1] (x_recv_rdy=0, x_fifo_wen:[0,0,0,0])
  await d2c(dut, 1, 0, [1,1,1,1], [0,0,0,0], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 0, 1, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

@cocotb.test()
async def test_load_w(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # w_recv_val=0, w_fifo_full=[0,0,0,0] (w_recv_rdy=1, w_fifo_wen:[0,0,0,0])
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 1, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # w_recv_val=1, w_fifo_full=[0,0,0,0] (w_recv_rdy=1, w_fifo_wen:[1,1,1,1])
  await d2c(dut, 0, 1, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 0, 1, 1, [0,0,0,0], [1,1,1,1])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # w_recv_val=0, w_fifo_full=[1,1,1,1] (w_recv_rdy=0, w_fifo_wen:[0,0,0,0])
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 0, 1, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # w_recv_val=1, w_fifo_full=[1,1,1,1] (w_recv_rdy=0, w_fifo_wen:[0,0,0,0])
  await d2c(dut, 0, 1, [0,0,0,0], [1,1,1,1], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 0, 1, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

@cocotb.test()
async def test_fsm_directed(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # x_fifo_full:[1,1,1,1], w_fifo_full:[1,1,1,1]
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 0, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, LOAD, [0,0,0,0], [0,0,0,0])

  # MAC (t=0: read-enable first FIFO)
  await d2c(dut, 0, 0, [1,1,1,1], [0,0,0,0], [1,1,1,1], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,0,0,0], [1,0,0,0])

  # MAC (t=1: read-enable second FIFO, lose fifo_full status)
  await d2c(dut, 0, 0, [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,0,0], [1,1,0,0])

  # MAC (t=2: read-enable third FIFO)
  await d2c(dut, 0, 0, [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,0], [1,1,1,0])

  # MAC (t=3: read-enable fourth FIFO)
  await d2c(dut, 0, 0, [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # MAC (t=4: first FIFO is empty)
  await d2c(dut, 0, 0, [0,0,0,0], [1,0,0,0], [0,0,0,0], [1,0,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # MAC (t=5: second FIFO is empty)
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,0,0], [0,0,0,0], [1,1,0,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # MAC (t=6: third FIFO is empty)
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,0], [0,0,0,0], [1,1,1,0])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # MAC (t=6: fourth FIFO is empty)
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, MAC, [1,1,1,1], [1,1,1,1])

  # OUT (mac_en=1 to allow remaining data flow)
  await d2c(dut, 0, 0, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])
  await always_comb(dut, 1, 0, 0, [0,0,0,0], [0,0,0,0])
  await always_ff(dut, OUT, [0,0,0,0], [0,0,0,0])

@cocotb.test()
async def test_fsm_random(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  for trials in range(100):
    # d2c
    x_recv_val   = 0
    w_recv_val   = 0
    x_fifo_full  = [0,0,0,0]
    x_fifo_empty = [1,1,1,1]
    w_fifo_full  = [0,0,0,0]
    w_fifo_empty = [1,1,1,1]

    # always_comb
    mac_en     = 0
    x_recv_rdy = 1
    w_recv_rdy = 1
    x_fifo_wen = [0,0,0,0]
    w_fifo_wen = [0,0,0,0]

    # always_ff
    state      = LOAD
    x_fifo_ren = [0,0,0,0]
    w_fifo_ren = [0,0,0,0]

    await reset(dut)
    await reset(dut)
    await reset(dut)

    state_out_count = 0

    while(state_out_count < 10):
      # update d2c

      x_recv_val = random.randint(0, 1)
      w_recv_val = random.randint(0, 1)

      for i in range(size):
        x_fifo_full[i]  = random.randint(0, 1)
        x_fifo_empty[i] = random.randint(0, 1)
        w_fifo_full[i]  = random.randint(0, 1)
        w_fifo_empty[i] = random.randint(0, 1)

      x_full = 1
      w_full = 1
      empty  = 1
      
      for i in range(size):
        x_full = (x_full & x_fifo_full[i])
        w_full = (w_full & w_fifo_full[i])
        empty  = (empty & x_fifo_empty[i] & w_fifo_empty[i])
      
      full = (x_full & w_full)

      # update combinational signals

      mac_en = ((state == MAC) | (state == OUT))
    
      x_recv_rdy = ((state == LOAD) & (x_full == 0))
      w_recv_rdy = ((state == LOAD) & (w_full == 0))

      for i in range(size):
        x_fifo_wen[i] = ((state == LOAD) & (x_full == 0) & x_recv_val)
        w_fifo_wen[i] = ((state == LOAD) & (w_full == 0) & w_recv_val)

      # verify

      await d2c(dut, x_recv_val, w_recv_val, x_fifo_full, x_fifo_empty, w_fifo_full, w_fifo_empty)
      await always_comb(dut, mac_en, x_recv_rdy, w_recv_rdy, x_fifo_wen, w_fifo_wen)
      await always_ff(dut, state, x_fifo_ren, w_fifo_ren)

      # update sequential signals

      x_fifo_ren[0] = (((state == LOAD) & full) | ((state == MAC) & (empty == 0)))
      w_fifo_ren[0] = (((state == LOAD) & full) | ((state == MAC) & (empty == 0)))
      
      for i in range(size-1, 0, -1):
        x_fifo_ren[i] = ((state == MAC) & (empty == 0) & x_fifo_ren[i-1])
        w_fifo_ren[i] = ((state == MAC) & (empty == 0) & w_fifo_ren[i-1])

      if ((state == LOAD) & full):
        state = MAC
      elif((state == MAC) & empty):
        state = OUT
      
      state_out_count += (state == OUT)