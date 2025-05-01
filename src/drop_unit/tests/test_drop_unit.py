import random

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

async def enable_test(dut, NUM_BITS, NUM_LOOPS, DROP_RATE):
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 1
    dut.enable.value = 1
    dut.enable_val.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    dut.enable.value = 0
    dut.enable_val.value = 0
    
    for i in range(NUM_LOOPS):
        for j in range(DROP_RATE):
            dut.req_val.value = 1
            dut.req_msg.value = random.getrandbits(NUM_BITS)

            await ClockCycles(dut.clk, 1)

            assert dut.resp_msg.value == dut.req_msg.value
            assert dut.resp_val.value == 1
        
        

async def drop_test(dut, NUM_BITS, NUM_LOOPS, DROP_RATE):
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 1
    dut.enable.value = 0
    dut.enable_val.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    dut.enable.value = 1
    dut.enable_val.value = 0

    dut.cfg_drop_val.value = 1
    dut.cfg_drop_msg.value = DROP_RATE

    for i in range(NUM_LOOPS):
        dut.req_val.value = 1
        dut.req_msg.value = random.getrandbits(NUM_BITS)
        dut.resp_rdy.value = 1

        await ClockCycles(dut.clk, 1)
        dut.cfg_drop_val.value = 0

        assert dut.resp_val.value == 1
        assert dut.resp_msg.value == dut.req_msg.value

        for j in range(DROP_RATE-1):
            dut.req_val.value = 1
            dut.req_msg.value = random.getrandbits(NUM_BITS)
            dut.resp_rdy.value = 0

            await ClockCycles(dut.clk, 1)
            
            assert dut.resp_val.value == 0

    dut.req_val.value = 0
        
        
N_BITS = 8
MAX_N_CYCLES = 10

random.seed(2)

@cocotb.test()
async def run_enable_test_1(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    for i in range(100):
        await enable_test(dut, N_BITS, random.randint(1,25), random.randint(2, MAX_N_CYCLES))

@cocotb.test()
async def run_drop_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    for i in range(100):
        await drop_test(dut, N_BITS, random.randint(1, 25), random.randint(2, MAX_N_CYCLES))

@cocotb.test()
async def run_enable_test_2(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    for i in range(100):
        await enable_test(dut, N_BITS, random.randint(1,25), random.randint(2, MAX_N_CYCLES))