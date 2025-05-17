#!/usr/bin/env python3

import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

size=4 # 4x4 systolic array
n=16   # Q8.8
d=8    # Q8.8

tcycles = size*2-1 # throughput cycle count for driving x and w

#===========================================================

def rand_fp(n, d):
    return Fixed(random.randint(0, (1 << n) - 1), 1, n, d, raw=True)

def mul_fp(a: Fixed, b: Fixed):
  return (a * b).resize(None, a._n, a._d)

def add_fp(a: Fixed, b: Fixed):
  return (a + b).resize(None, a._n, a._d)

def matmul_fp(x:[], w:[]):
  s = []
  for i in range(size):
    _s = []
    for j in range(size):
      _s.append(Fixed(0, 1, 16, 8))
    s.append(_s)

  for i in range(size):
    for j in range(size):
      for k in range(size):
        s[i][j] = add_fp(s[i][j], mul_fp(x[i][k], w[k][j]))
  
  return s

#===========================================================

async def reset(dut):
  dut.rst.value    = 1
  dut.mac_en.value = 0
  for i in range(size):
    dut.x_fifo_wen[i].value = 0
    dut.x_fifo_ren[i].value = 0
    dut.w_fifo_wen[i].value = 0
    dut.w_fifo_ren[i].value = 0
  await RisingEdge(dut.clk)
  dut.rst.value = 0

async def write_fifo(dut, l_x_col_in:[], t_w_row_in:[]):
  dut.rst.value    = 0
  dut.mac_en.value = 0

  for i in range(size):
    dut.l_x_col_in[i].value = l_x_col_in[i].get()
    dut.t_w_row_in[i].value = t_w_row_in[i].get()

    dut.x_fifo_wen[i].value = 1
    dut.x_fifo_ren[i].value = 0
    dut.w_fifo_wen[i].value = 1
    dut.w_fifo_ren[i].value = 0

  await RisingEdge(dut.clk)

async def mac(dut, x_fifo_ren:[], w_fifo_ren:[]):
  dut.rst.value    = 0
  dut.mac_en.value = 1

  for i in range(0, size):
    dut.x_fifo_ren[i].value = x_fifo_ren[i]
    dut.w_fifo_ren[i].value = w_fifo_ren[i]

  await RisingEdge(dut.clk)

async def check_fifo_status(dut, x_fifo_full:[], x_fifo_empty:[], w_fifo_full:[], w_fifo_empty:[]):
  dut.rst.value    = 0
  dut.mac_en.value = 0

  for i in range(size):
    dut.x_fifo_wen[i].value = 0
    dut.x_fifo_ren[i].value = 0
    dut.w_fifo_wen[i].value = 0
    dut.w_fifo_ren[i].value = 0
  
  await RisingEdge(dut.clk)

  for i in range(size):
    assert (dut.x_fifo_full[i].value == x_fifo_full[i])
    assert (dut.x_fifo_empty[i].value == x_fifo_empty[i])
    assert (dut.w_fifo_full[i].value == w_fifo_full[i])
    assert (dut.w_fifo_empty[i].value == w_fifo_empty[i])

async def check_output(dut, row, col, ref):
  dut.rst.value      = 0
  dut.mac_en.value   = 0
  for i in range(size):
    dut.x_fifo_wen[i].value = 0
    dut.x_fifo_ren[i].value = 0
    dut.w_fifo_wen[i].value = 0
    dut.w_fifo_ren[i].value = 0

  dut.out_rsel.value = row
  dut.out_csel.value = col
  
  await RisingEdge(dut.clk)
  assert (dut.b_s_out.value == ref.get()),          \
    "FAILED: dut ({}) != ref ({}) @ ({}, {})"       \
    .format(dut.b_s_out.value, ref.get(), row, col)

#===========================================================
# test_case_dpath_4x4
#===========================================================

@cocotb.test()
async def test_case_dpath_4x4(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  trials = 3

  for t in range(trials):
    # randomly initialize 4x4 input and weight
    x = []
    w = []
    for i in range(size):
      x_row = []
      w_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(16, 8), 1, 16, 8))
        w_row.append(Fixed(rand_fp(16, 8), 1, 16, 8))
      x.append(x_row)
      w.append(w_row)
    
    # compute reference matmul
    s_ref = matmul_fp(x, w)

    await reset(dut)
    
    x_fifo_full  = [0, 0, 0, 0]
    x_fifo_empty = [1, 1, 1, 1]
    w_fifo_full  = [0, 0, 0, 0]
    w_fifo_empty = [1, 1, 1, 1]

    x_fifo_ren = [0, 0, 0, 0]
    w_fifo_ren = [0, 0, 0, 0]

    await check_fifo_status(dut, x_fifo_full, x_fifo_empty, w_fifo_full, w_fifo_empty)
    await check_fifo_status(dut, x_fifo_full, x_fifo_empty, w_fifo_full, w_fifo_empty)
    await check_fifo_status(dut, x_fifo_full, x_fifo_empty, w_fifo_full, w_fifo_empty)

    # fill tensor and weigth FIFOs (CMO, RMO)
    for _t in range(size):
      l_x_col_in = []
      for i in range(size):
        l_x_col_in.append(x[i][_t])
      t_w_row_in = []
      for j in range(size):
        t_w_row_in.append(w[_t][j])
      
      await write_fifo(dut, l_x_col_in, t_w_row_in)

      if (_t == 0):
        x_fifo_empty = [0, 0, 0, 0]
        w_fifo_empty = [0, 0, 0, 0]
      if (_t == size-1):
        x_fifo_full  = [1, 1, 1, 1]
        w_fifo_full  = [1, 1, 1, 1]
      
      await check_fifo_status(dut, x_fifo_full, x_fifo_empty, w_fifo_full, w_fifo_empty)
    
    # enable MAC
    x_fifo_ren[0] = 1
    w_fifo_ren[0] = 1
    for _t in range(tcycles+size+1):
      await mac(dut, x_fifo_ren, w_fifo_ren)
      for i in range(size-1, 0, -1):
        x_fifo_ren[i] = x_fifo_ren[i-1]
        w_fifo_ren[i] = w_fifo_ren[i-1]
    
    await check_fifo_status(dut, [0,0,0,0], [1,1,1,1], [0,0,0,0], [1,1,1,1])

    # check PE outputs individually
    for i in range(size):
      for j in range(size):
        await check_output(dut, i, j, s_ref[i][j])