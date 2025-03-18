import math
import random
import cocotb
import subprocess
import numpy as np
from fixedpt import Fixed
from cocotb.triggers import *
from cocotb.clock import Clock

depth = 16
nbits = 16
dbits = 8

#===========================================================

def rand_fp(n, d):
    return Fixed(random.randint(0, (1 << n) - 1), 1, n, d, raw=True)

#===========================================================

async def reset(dut):
  dut.rst.value = 1
  await RisingEdge(dut.clk)
  dut.rst.value = 0

async def rw_ptr_step(dut, wen, ren, full, empty):
  dut.rst.value = 0
  dut.wen.value = wen
  dut.ren.value = ren

  await RisingEdge(dut.clk)

  assert (dut.full.value == full),             \
    "FAILED: dut.full ({}) != ref.full ({})"   \
    .format(dut.full.value, full)
  assert (dut.empty.value == empty),           \
    "FAILED: dut.empty ({}) != ref.empty ({})" \
    .format(dut.empty.value, empty)

async def step(dut, wen, ren, d, q, full, empty):
  dut.rst.value = 0
  dut.wen.value = wen
  dut.ren.value = ren
  dut.d.value   = d

  await RisingEdge(dut.clk)

  assert(dut.q.value == q),                    \
    "FAILED: dut.q ({}) != ref.q ({})"         \
    .format(dut.q.value, q)
  assert (dut.full.value == full),             \
    "FAILED: dut.full ({}) != ref.full ({})"   \
    .format(dut.full.value, full)
  assert (dut.empty.value == empty),           \
    "FAILED: dut.empty ({}) != ref.empty ({})" \
    .format(dut.empty.value, empty)

#===========================================================
# test_case_1_simple_rw_ptr_step
#===========================================================

@cocotb.test()
async def test_case_1_simple_rw_ptr_step(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  for T in range(10000):
    #                     wen ren full empty
    await rw_ptr_step(dut, 1,  0,  0,    1  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 1,  0,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  1,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )
    await rw_ptr_step(dut, 0,  1,  0,    0  )

#===========================================================
# test_case_2_random_rw_ptr_step
#===========================================================

@cocotb.test()
async def test_case_2_random_rw_ptr_step(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  full       = 0
  empty      = 1
  curr_depth = 0

  for T in range(1000000):
    wen = random.randint(0, 1)
    ren = random.randint(0, 1)

    await rw_ptr_step(dut, wen, ren, full, empty)

    curr_depth += int(wen & (wen ^ full)) - int(ren & (ren ^ empty))

    full  = int(curr_depth == depth)
    empty = int(curr_depth == 0)

#===========================================================
# test_case_3_simple_rw
#===========================================================

@cocotb.test()
async def test_case_3_simple_rw(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  istream = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  ostream = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

  await reset(dut)

  # istream
  await step(dut, 1, 0, istream[0],  0, 0, 1)
  await step(dut, 1, 0, istream[1],  0, 0, 0)
  await step(dut, 1, 0, istream[2],  0, 0, 0)
  await step(dut, 1, 0, istream[3],  0, 0, 0)
  await step(dut, 1, 0, istream[4],  0, 0, 0)
  await step(dut, 1, 0, istream[5],  0, 0, 0)
  await step(dut, 1, 0, istream[6],  0, 0, 0)
  await step(dut, 1, 0, istream[7],  0, 0, 0)
  await step(dut, 1, 0, istream[8],  0, 0, 0)
  await step(dut, 1, 0, istream[9],  0, 0, 0)
  await step(dut, 1, 0, istream[10], 0, 0, 0)
  await step(dut, 1, 0, istream[11], 0, 0, 0)
  await step(dut, 1, 0, istream[12], 0, 0, 0)
  await step(dut, 1, 0, istream[13], 0, 0, 0)
  await step(dut, 1, 0, istream[14], 0, 0, 0)
  await step(dut, 1, 0, istream[15], 0, 0, 0)

  # check full signal
  await step(dut, 0, 0, 0, 0, 1, 0)

  # ostream
  await step(dut, 0, 1, 0, ostream[0],  1, 0)
  await step(dut, 0, 1, 0, ostream[1],  0, 0)
  await step(dut, 0, 1, 0, ostream[2],  0, 0)
  await step(dut, 0, 1, 0, ostream[3],  0, 0)
  await step(dut, 0, 1, 0, ostream[4],  0, 0)
  await step(dut, 0, 1, 0, ostream[5],  0, 0)
  await step(dut, 0, 1, 0, ostream[6],  0, 0)
  await step(dut, 0, 1, 0, ostream[7],  0, 0)
  await step(dut, 0, 1, 0, ostream[8],  0, 0)
  await step(dut, 0, 1, 0, ostream[9],  0, 0)
  await step(dut, 0, 1, 0, ostream[10], 0, 0)
  await step(dut, 0, 1, 0, ostream[11], 0, 0)
  await step(dut, 0, 1, 0, ostream[12], 0, 0)
  await step(dut, 0, 1, 0, ostream[13], 0, 0)
  await step(dut, 0, 1, 0, ostream[14], 0, 0)
  await step(dut, 0, 1, 0, ostream[15], 0, 0)

  # check empty signal
  await step(dut, 0, 0, 0, 0, 0, 1)

#===========================================================
# test_case_4_read_empty
#===========================================================

@cocotb.test()
async def test_case_4_read_empty(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # FIFO output should always be zero if empty
  await step(dut, 0, 1, 0, 0, 0, 1)
  await step(dut, 0, 1, 0, 0, 0, 1)
  await step(dut, 0, 1, 0, 0, 0, 1)

#===========================================================
# test_case_5_read_enable
#===========================================================

@cocotb.test()
async def test_case_5_read_enable(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # write FIFO with some values  
  await step(dut, 1, 0, 0xAA, 0, 0, 1)
  await step(dut, 1, 0, 0xBB, 0, 0, 0)
  await step(dut, 1, 0, 0xCC, 0, 0, 0)

  # read some values in FIFO
  await step(dut, 0, 1, 0, 0xAA, 0, 0)
  await step(dut, 0, 1, 0, 0xBB, 0, 0)

  # FIFO should always output zero if read is not enabled
  await step(dut, 0, 0, 0, 0, 0, 0)
  await step(dut, 0, 0, 0, 0, 0, 0)
  await step(dut, 0, 0, 0, 0, 0, 0)

#===========================================================
# test_case_6_write_full
#===========================================================

@cocotb.test()
async def test_case_6_write_full(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  istream = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  ostream = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

  await reset(dut)

  # istream
  await step(dut, 1, 0, istream[0],  0, 0, 1)
  await step(dut, 1, 0, istream[1],  0, 0, 0)
  await step(dut, 1, 0, istream[2],  0, 0, 0)
  await step(dut, 1, 0, istream[3],  0, 0, 0)
  await step(dut, 1, 0, istream[4],  0, 0, 0)
  await step(dut, 1, 0, istream[5],  0, 0, 0)
  await step(dut, 1, 0, istream[6],  0, 0, 0)
  await step(dut, 1, 0, istream[7],  0, 0, 0)
  await step(dut, 1, 0, istream[8],  0, 0, 0)
  await step(dut, 1, 0, istream[9],  0, 0, 0)
  await step(dut, 1, 0, istream[10], 0, 0, 0)
  await step(dut, 1, 0, istream[11], 0, 0, 0)
  await step(dut, 1, 0, istream[12], 0, 0, 0)
  await step(dut, 1, 0, istream[13], 0, 0, 0)
  await step(dut, 1, 0, istream[14], 0, 0, 0)
  await step(dut, 1, 0, istream[15], 0, 0, 0)

  # check full signal
  await step(dut, 0, 0, 0, 0, 1, 0)

  # check FIFO is not being overwritten when full
  await step(dut, 1, 0, rand_fp(nbits, dbits).get(), 0, 1, 0)
  await step(dut, 1, 0, rand_fp(nbits, dbits).get(), 0, 1, 0)
  await step(dut, 1, 0, rand_fp(nbits, dbits).get(), 0, 1, 0)
  await step(dut, 1, 0, rand_fp(nbits, dbits).get(), 0, 1, 0)
  await step(dut, 1, 0, rand_fp(nbits, dbits).get(), 0, 1, 0)

  # ostream
  await step(dut, 0, 1, 0, ostream[0],  1, 0)
  await step(dut, 0, 1, 0, ostream[1],  0, 0)
  await step(dut, 0, 1, 0, ostream[2],  0, 0)
  await step(dut, 0, 1, 0, ostream[3],  0, 0)
  await step(dut, 0, 1, 0, ostream[4],  0, 0)
  await step(dut, 0, 1, 0, ostream[5],  0, 0)
  await step(dut, 0, 1, 0, ostream[6],  0, 0)
  await step(dut, 0, 1, 0, ostream[7],  0, 0)
  await step(dut, 0, 1, 0, ostream[8],  0, 0)
  await step(dut, 0, 1, 0, ostream[9],  0, 0)
  await step(dut, 0, 1, 0, ostream[10], 0, 0)
  await step(dut, 0, 1, 0, ostream[11], 0, 0)
  await step(dut, 0, 1, 0, ostream[12], 0, 0)
  await step(dut, 0, 1, 0, ostream[13], 0, 0)
  await step(dut, 0, 1, 0, ostream[14], 0, 0)
  await step(dut, 0, 1, 0, ostream[15], 0, 0)

  # check empty signal
  await step(dut, 0, 0, 0, 0, 0, 1)

#===========================================================
# test_case_7_write_enable
#===========================================================

@cocotb.test()
async def test_case_7_write_enable(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  await reset(dut)

  # FIFO should only be written when write is enabled
  await step(dut, 1, 0, 0xAA, 0, 0, 1)
  await step(dut, 0, 0, 0xBB, 0, 0, 0)
  await step(dut, 1, 0, 0xCC, 0, 0, 0)

  await step(dut, 0, 1, 0, 0xAA, 0, 0)
  await step(dut, 0, 1, 0, 0xCC, 0, 0)

  await step(dut, 0, 1, 0, 0x00, 0, 1)
  await step(dut, 0, 1, 0, 0x00, 0, 1)
  await step(dut, 0, 1, 0, 0x00, 0, 1)

#===========================================================
# test_case_8_random_rw
#===========================================================

@cocotb.test()
async def test_case_8_random_rw(dut):
  cocotb.start_soon(Clock(dut.clk, 1, units="ns").start(start_high=False))

  stream     = []
  stream_idx = 0
  full       = 0
  empty      = 1
  curr_depth = 0

  await reset(dut)

  for T in range(1000000):
    wen = random.randint(0, 1)
    ren = random.randint(0, 1)
    d   = rand_fp(nbits, dbits).get()
    q   = 0

    if (ren & (ren ^ empty)):
      q = stream[stream_idx]
      stream_idx += 1

    await step(dut, wen, ren, d, q, full, empty)

    curr_depth += int(wen & (wen ^ full)) - int(ren & (ren ^ empty))

    if (wen & (wen ^ full)):
      stream.append(d)

    full  = int(curr_depth == depth)
    empty = int(curr_depth == 0)