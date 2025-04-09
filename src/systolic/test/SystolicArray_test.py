import math
import random
import cocotb
import subprocess
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
  dut.rst.value        = 1
  dut.x_recv_val.value = 0
  dut.w_recv_val.value = 0
  await RisingEdge(dut.clk)
  dut.rst.value = 0

async def load_x(dut, l_x_col_in:[]):
  dut.x_recv_val.value = 1
  for i in range(size):
    dut.l_x_col_in[i].value = l_x_col_in[i].get()

async def load_w(dut, t_w_row_in:[]):
  dut.w_recv_val.value = 1
  for i in range(size):
    dut.t_w_row_in[i].value = t_w_row_in[i].get()

async def step(dut):
  await RisingEdge(dut.clk)
  dut.x_recv_val.value = 0
  dut.w_recv_val.value = 0

async def check_recv_rdy(dut, x_recv_rdy, w_recv_rdy):
  assert (dut.x_recv_rdy.value == x_recv_rdy)
  assert (dut.w_recv_rdy.value == w_recv_rdy)

#===========================================================

@cocotb.test()
async def test_case_1_reset(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)
  await reset(dut)
  await reset(dut)

#===========================================================

@cocotb.test()
async def test_case_2_load_x(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  trials = 100

  for trial in range(trials):
    x = []
    for i in range(size):
      x_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(16, 8), 1, 16, 8))
      x.append(x_row)

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    for t in range(size):
      l_x_col_in = []
      for i in range(size):
        l_x_col_in.append(x[i][t])
      
      await load_x(dut, l_x_col_in)
      
      await step(dut)
      await check_recv_rdy(dut, 1, 1)
    
    await step(dut)
    await check_recv_rdy(dut, 0, 1)