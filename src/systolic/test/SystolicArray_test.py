import math
import random
import cocotb
import subprocess
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

# FP Q8.8
NBITS=16
DBITS=8

#===========================================================

def rand_fp(n, d):
    return Fixed(random.randint(0, (1 << n) - 1), 1, n, d, raw=True)

def mul_fp(a: Fixed, b: Fixed):
  return (a * b).resize(None, a._n, a._d)

def add_fp(a: Fixed, b: Fixed):
  return (a + b).resize(None, a._n, a._d)

def matmul_fp(x:[], w:[], size):
  s = []
  for i in range(size):
    _s = []
    for j in range(size):
      _s.append(Fixed(0, 1, NBITS, DBITS))
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

async def load_x(dut, l_x_col_in:[], size):
  dut.x_recv_val.value = 1
  for i in range(size):
    dut.l_x_col_in[i].value = l_x_col_in[i].get()

async def load_w(dut, t_w_row_in:[], size):
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

async def check_mac_rdy(dut, mac_rdy):
  assert (dut.mac_rdy.value == mac_rdy)

async def check_out_rdy(dut, out_rdy):
  assert (dut.out_rdy.value == out_rdy)

async def check_output(dut, row, col, ref):
  dut.out_rsel.value = row
  dut.out_csel.value = col
  await Timer(1, units="ns")
  assert (dut.b_s_out.value == ref.get())

#===========================================================

@cocotb.test()
async def test_case_1_reset(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)
  await reset(dut)
  await reset(dut)

#===========================================================

@cocotb.test()
async def test_case_2_load_x(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  trials = 100

  for trial in range(trials):
    x = []
    for i in range(size):
      x_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      x.append(x_row)

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    for t in range(size):
      l_x_col_in = []
      for i in range(size):
        l_x_col_in.append(x[i][t])
      
      await load_x(dut, l_x_col_in, size)
      
      await step(dut)
      await check_recv_rdy(dut, 1, 1)
    
    await step(dut)
    await check_recv_rdy(dut, 0, 1)

#===========================================================

@cocotb.test()
async def test_case_3_load_w(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  trials = 100

  for trial in range(trials):
    w = []
    for i in range(size):
      w_row = []
      for j in range(size):
        w_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      w.append(w_row)

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    for t in range(size):
      t_w_row_in = []
      for i in range(size):
        t_w_row_in.append(w[t][i])
      
      await load_w(dut, t_w_row_in, size)

      await step(dut)
      await check_recv_rdy(dut, 1, 1)
    
    await step(dut)
    await check_recv_rdy(dut, 1, 0)

#===========================================================

@cocotb.test()
async def test_case_4_synchronous_load(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  for trial in range(100):
    x = []
    w = []
    for i in range(size):
      x_row = []
      w_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
        w_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      x.append(x_row)
      w.append(w_row)
      
    l_x_col_in_idx = size-1
    t_w_row_in_idx = size-1

    x_recv_rdy = 1
    w_recv_rdy = 1

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    while(x_recv_rdy | w_recv_rdy):
      # select x column, w row
      l_x_col_in = []
      t_w_row_in = []
      for i in range(size):
        if(x_recv_rdy):
          l_x_col_in.append(x[i][l_x_col_in_idx])
        if(w_recv_rdy):
          t_w_row_in.append(w[t_w_row_in_idx][i])
        
      # load x, w
      if(x_recv_rdy):
        await load_x(dut, l_x_col_in, size)
        l_x_col_in_idx -= 1
      if(w_recv_rdy):
        await load_w(dut, t_w_row_in, size)
        t_w_row_in_idx -= 1
        
      await step(dut)
      await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

      x_recv_rdy = (l_x_col_in_idx >= 0)
      w_recv_rdy = (t_w_row_in_idx >= 0)
      
    await step(dut)
    await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

#===========================================================

@cocotb.test()
async def test_case_5_asynchronous_load(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  for trial in range(100):
    x = []
    w = []
    for i in range(size):
      x_row = []
      w_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
        w_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      x.append(x_row)
      w.append(w_row)
    
    l_x_col_in_idx = size-1
    t_w_row_in_idx = size-1

    x_recv_rdy = 1
    w_recv_rdy = 1

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    while(x_recv_rdy | w_recv_rdy):
      # randomly choose to load x, w
      load_x_sel = random.randint(0, 1)
      load_w_sel = random.randint(0, 1)
      
      # select x column, w row
      l_x_col_in = []
      t_w_row_in = []
      for i in range(size):
        if(x_recv_rdy & load_x_sel):
          l_x_col_in.append(x[i][l_x_col_in_idx])
        if(w_recv_rdy & load_w_sel):
          t_w_row_in.append(w[t_w_row_in_idx][i])
      
      # load x, w
      if(x_recv_rdy & load_x_sel):
        await load_x(dut, l_x_col_in, size)
        l_x_col_in_idx -= 1
      if(w_recv_rdy & load_w_sel):
        await load_w(dut, t_w_row_in, size)
        t_w_row_in_idx -= 1
      
      await step(dut)
      await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

      x_recv_rdy = (l_x_col_in_idx >= 0)
      w_recv_rdy = (t_w_row_in_idx >= 0)
    
    await step(dut)
    await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

#===========================================================

@cocotb.test()
async def test_case_6_synchronous_load_mac_out(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  for trial in range(100):
    x = []
    w = []
    for i in range(size):
      x_row = []
      w_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
        w_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      x.append(x_row)
      w.append(w_row)
    
    s_ref = matmul_fp(x, w, size)

    # LOAD

    l_x_col_in_idx = size-1
    t_w_row_in_idx = size-1

    x_recv_rdy = 1
    w_recv_rdy = 1

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    while(x_recv_rdy | w_recv_rdy):
      # select x column, w row
      l_x_col_in = []
      t_w_row_in = []
      for i in range(size):
        if(x_recv_rdy):
          l_x_col_in.append(x[i][l_x_col_in_idx])
        if(w_recv_rdy):
          t_w_row_in.append(w[t_w_row_in_idx][i])
          
      # load x, w
      if(x_recv_rdy):
        await load_x(dut, l_x_col_in, size)
        l_x_col_in_idx -= 1
      if(w_recv_rdy):
        await load_w(dut, t_w_row_in, size)
        t_w_row_in_idx -= 1
          
      await step(dut)
      await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

      x_recv_rdy = (l_x_col_in_idx >= 0)
      w_recv_rdy = (t_w_row_in_idx >= 0)
        
    await step(dut)
    await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)
    await check_mac_rdy(dut, 0)
    await check_out_rdy(dut, 0)

    # MAC

    throughput_cycles     = (size * 2)
    output_latency_cycles = (size - 1)

    for t in range(throughput_cycles + output_latency_cycles):
      # drive in all of x and w into PEs
      await step(dut)
      await check_recv_rdy(dut, 0, 0)
      await check_mac_rdy(dut, 1)
      await check_out_rdy(dut, 0)
    
    # OUT

    for i in range(size):
      for j in range(size):
        # combinationally check final summation stored in each PE
        await step(dut)
        await check_recv_rdy(dut, 0, 0)
        await check_mac_rdy(dut, 0)
        await check_out_rdy(dut, 1)
        await check_output(dut, i, j, s_ref[i][j])

#===========================================================

@cocotb.test()
async def test_case_7_asynchronous_load_mac_out(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  for trial in range(100):
    x = []
    w = []
    for i in range(size):
      x_row = []
      w_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
        w_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      x.append(x_row)
      w.append(w_row)
    
    s_ref = matmul_fp(x, w, size)

    # LOAD

    l_x_col_in_idx = size-1
    t_w_row_in_idx = size-1

    x_recv_rdy = 1
    w_recv_rdy = 1

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    while(x_recv_rdy | w_recv_rdy):
      # randomly choose to load x, w
      load_x_sel = random.randint(0, 1)
      load_w_sel = random.randint(0, 1)

      # select x column, w row
      l_x_col_in = []
      t_w_row_in = []
      for i in range(size):
        if(x_recv_rdy & load_x_sel):
          l_x_col_in.append(x[i][l_x_col_in_idx])
        if(w_recv_rdy & load_w_sel):
          t_w_row_in.append(w[t_w_row_in_idx][i])
          
      # load x, w
      if(x_recv_rdy & load_x_sel):
        await load_x(dut, l_x_col_in, size)
        l_x_col_in_idx -= 1
      if(w_recv_rdy & load_w_sel):
        await load_w(dut, t_w_row_in, size)
        t_w_row_in_idx -= 1
          
      await step(dut)
      await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

      x_recv_rdy = (l_x_col_in_idx >= 0)
      w_recv_rdy = (t_w_row_in_idx >= 0)
        
    await step(dut)
    await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)
    await check_mac_rdy(dut, 0)
    await check_out_rdy(dut, 0)

    # MAC

    throughput_cycles     = (size * 2)
    output_latency_cycles = (size - 1)

    for t in range(throughput_cycles + output_latency_cycles):
      # drive in all of x and w into PEs
      await step(dut)
      await check_recv_rdy(dut, 0, 0)
      await check_mac_rdy(dut, 1)
      await check_out_rdy(dut, 0)
    
    # OUT

    for i in range(size):
      for j in range(size):
        # combinationally check final summation stored in each PE
        await step(dut)
        await check_recv_rdy(dut, 0, 0)
        await check_mac_rdy(dut, 0)
        await check_out_rdy(dut, 1)
        await check_output(dut, i, j, s_ref[i][j])

#===========================================================

@cocotb.test()
async def test_case_8_asynchronous_load_mac_out_edge(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  for trial in range(100):
    x = []
    w = []
    for i in range(size):
      x_row = []
      w_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
        w_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      x.append(x_row)
      w.append(w_row)
    
    s_ref = matmul_fp(x, w, size)

    # LOAD

    l_x_col_in_idx = size-1
    t_w_row_in_idx = size-1

    x_recv_rdy = 1
    w_recv_rdy = 1

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    while(x_recv_rdy | w_recv_rdy):
      # randomly choose to load x, w
      load_x_sel = random.randint(0, 1)
      load_w_sel = random.randint(0, 1)

      # select x column, w row
      # EDGE CASE: attempt to write FIFOs even if *_recv_rdy=0 (should be ignored)
      l_x_col_in = []
      t_w_row_in = []
      for i in range(size):
        if(load_x_sel):
          x_load = (x[i][l_x_col_in_idx] if x_recv_rdy else rand_fp(NBITS, DBITS))
          l_x_col_in.append(x_load)
        if(load_w_sel):
          w_load = (w[t_w_row_in_idx][i] if w_recv_rdy else rand_fp(NBITS, DBITS))
          t_w_row_in.append(w_load)
          
      # load x, w
      if(load_x_sel):
        await load_x(dut, l_x_col_in, size)
        l_x_col_in_idx -= 1
      if(load_w_sel):
        await load_w(dut, t_w_row_in, size)
        t_w_row_in_idx -= 1
          
      await step(dut)
      await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

      x_recv_rdy = (l_x_col_in_idx >= 0)
      w_recv_rdy = (t_w_row_in_idx >= 0)
        
    await step(dut)
    await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)
    await check_mac_rdy(dut, 0)
    await check_out_rdy(dut, 0)

    # MAC

    throughput_cycles     = (size * 2)
    output_latency_cycles = (size - 1)

    for t in range(throughput_cycles + output_latency_cycles):
      # drive in all of x and w into PEs
      await step(dut)
      await check_recv_rdy(dut, 0, 0)
      await check_mac_rdy(dut, 1)
      await check_out_rdy(dut, 0)
    
    # OUT
    
    for i in range(size):
      for j in range(size):
        # combinationally check final summation stored in each PE
        await step(dut)
        await check_recv_rdy(dut, 0, 0)
        await check_mac_rdy(dut, 0)
        await check_out_rdy(dut, 1)
        await check_output(dut, i, j, s_ref[i][j])

#===========================================================

@cocotb.test()
async def test_case_9_general(dut):
  size=len(dut.l_x_col_in)
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  for trial in range(1):
    x = []
    w = []
    for i in range(size):
      x_row = []
      w_row = []
      for j in range(size):
        x_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
        w_row.append(Fixed(rand_fp(NBITS, DBITS), 1, NBITS, DBITS))
      x.append(x_row)
      w.append(w_row)
    
    s_ref = matmul_fp(x, w, size)

    # LOAD

    l_x_col_in_idx = size-1
    t_w_row_in_idx = size-1

    x_recv_rdy = 1
    w_recv_rdy = 1

    await reset(dut)

    await step(dut)
    await check_recv_rdy(dut, 1, 1)

    while(x_recv_rdy | w_recv_rdy):
      # randomly choose to load x, w
      load_x_sel = random.randint(0, 1)
      load_w_sel = random.randint(0, 1)

      # select x column, w row
      l_x_col_in = []
      t_w_row_in = []
      for i in range(size):
        if(x_recv_rdy & load_x_sel):
          l_x_col_in.append(x[i][l_x_col_in_idx])
        if(w_recv_rdy & load_w_sel):
          t_w_row_in.append(w[t_w_row_in_idx][i])
          
      # load x, w
      if(x_recv_rdy & load_x_sel):
        await load_x(dut, l_x_col_in, size)
        l_x_col_in_idx -= 1
      if(w_recv_rdy & load_w_sel):
        await load_w(dut, t_w_row_in, size)
        t_w_row_in_idx -= 1
          
      await step(dut)
      await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)

      x_recv_rdy = (l_x_col_in_idx >= 0)
      w_recv_rdy = (t_w_row_in_idx >= 0)
        
    await step(dut)
    await check_recv_rdy(dut, x_recv_rdy, w_recv_rdy)
    await check_mac_rdy(dut, 0)
    await check_out_rdy(dut, 0)

    # MAC

    throughput_cycles     = (size * 2)
    output_latency_cycles = (size - 1)

    for t in range(throughput_cycles + output_latency_cycles):
      # drive in all of x and w into PEs
      await step(dut)
      await check_recv_rdy(dut, 0, 0)
      await check_mac_rdy(dut, 1)
      await check_out_rdy(dut, 0)
    
    # OUT

    for i in range(size):
      for j in range(size):
        # combinationally check final summation stored in each PE
        await step(dut)
        await check_recv_rdy(dut, 0, 0)
        await check_mac_rdy(dut, 0)
        await check_out_rdy(dut, 1)
        await check_output(dut, i, j, s_ref[i][j])