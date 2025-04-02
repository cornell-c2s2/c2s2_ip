import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

size = 16

#===========================================================

def d2c(dut, x_send_val, w_send_val, x_fifo_full, x_fifo_empty, w_fifo_full, w_fifo_empty):
  dut.rst.value = 0
  dut.x_send_val.value = x_send_val
  dut.w_send_val.value = w_send_val
  
  for i in range(size):
    dut.x_fifo_full[i].value  = x_fifo_full[i]
    dut.x_fifo_empty[i].value = x_fifo_empty[i]
    dut.w_fifo_full[i].value  = w_fifo_full[i]
    dut.w_fifo_empty[i].value = w_fifo_empty[i]

async def step(dut):
  await RisingEdge(dut.clk)

def c2d(dut, mac_en, x_send_rdy, w_send_rdy, x_fifo_wen, x_fifo_ren, w_fifo_wen, w_fifo_ren):
  assert (dut.mac_en.value == mac_en)
  assert (dut.x_send_rdy == x_send_rdy)
  assert (dut.w_send_rdy == w_send_rdy)
  
  for i in range(size):
    assert (dut.x_fifo_wen[i].value == x_fifo_wen[i])
    assert (dut.x_fifo_ren[i].value == x_fifo_ren[i])
    assert (dut.w_fifo_wen[i].value == w_fifo_wen[i])
    assert (dut.w_fifo_ren[i].value == w_fifo_ren[i])

def state(dut, state):
  assert (dut._state.value == state)

#===========================================================

