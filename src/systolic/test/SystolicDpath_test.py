#!/usr/bin/env python3

import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

size=3 # 3x3 systolic array
n=16   # Q8.8
d=8    # Q8.8

tcycles = size*2-1 # throughput cycle count for driving x and w

#===========================================================

def random_fp_16b():
  int_8b = np.random.randint(-2**7, 2**7)    # [-128, 127]
  dec_8b = np.random.randint(0, 2**8) / 2**8 # [0, 0.996]
  return int_8b + dec_8b

def fixed_point_multiply(a: Fixed, b: Fixed):
  return (a * b).resize(None, a._n, a._d)

def matmul(x:[], w:[]):
  print(x)
  print(w)

#===========================================================

async def reset(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)

async def check_output(dut, row, col, ref):
  dut.rst.value      = 0
  dut.en.value       = 0
  dut.out_rsel.value = row
  dut.out_csel.value = col
  
  await RisingEdge(dut.clk)
  assert (dut.b_s_out.value == ref.get()),          \
    "FAILED: dut ({}) != ref ({}) @ ({}, {})"       \
    .format(dut.b_s_out.value, ref.get(), row, col)

async def step(dut, x_in:[], w_in:[]):
  dut.rst.value = 0
  dut.en.value  = 1
  
  for i in range(SIZE):
    dut.l_x_in[i].value = x_in[i].get()
    dut.t_w_in[i].value = w_in[i].get()
  
  await RisingEdge(dut.clk)

#===========================================================
# test_case_1_ideal_flow
#===========================================================

@cocotb.test()
async def test_case_1_ideal_flow(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  x = []
  w = []

  for i in range(size):
    x_row = []
    w_row = []
    for j in range(size):
      x_row.append(Fixed(random_fp_16b(), 1, 16, 8))
      w_row.append(Fixed(random_fp_16b(), 1, 16, 8))
    x.append(x_row)
    w.append(w_row)
  
  await reset(dut)

  # ideally flow inputs and weights with zero buffers

  x_in   = []
  w_in   = []
  x_csel = []
  w_rsel = []

  for i in range(size):
    x_in.append(0)
    w_in.append(0)
    x_csel.append(size-1)
    w_rsel.append(size-1)

  for cycle in range(tcycles):
    
    for r in range(size):
      if (r <= cycle) & (x_csel[r] >= 0):
        x_in[r] = x[r][x_csel[r]]
        x_csel[r] -= 1
      else:
        x_in[r] = Fixed(0, 1, 16, 8)
    
    for c in range(size):
      if (c <= cycle) & (w_rsel[c] >= 0):
        w_in[c] = w[w_rsel[c]][c]
        w_rsel[c] -= 1
      else:
        w_in[c] = Fixed(0, 1, 16, 8)
    
    print("x_in:{}\nw_in:{}\n" .format(x_in, w_in))