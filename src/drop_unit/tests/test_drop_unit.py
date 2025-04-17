import random

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

'''
@cocotb.test()
async def enable_basic_test_1(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)
    
    dut.enable.value = 1
    
    dut.cfg_drop_val.value = 1
    dut.cfg_drop_msg.value = 10
    
    for i in range(5):
        for j in range(9):
            dut.req_val.value = 1
            dut.req_msg.value = j+1
            assert(dut.resp_msg.value == dut.req_msg.value)
            await ClockCycles(dut.clk, 1)
        dut.req_val.value = 1
        dut.req_msg.value = 10
        assert(dut.resp_msg.value == dut.req_msg.value)
        await ClockCycles(dut.clk, 1)
'''
async def enable_basic_test_2(dut, NUM_BITS, NUM_LOOPS, DROP_RATE):
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)
    
    dut.enable.value = 1
    
    #dut.cfg_drop_val.value = 1
    #dut.cfg_drop_msg.value = DROP_RATE
    
    for i in range(NUM_LOOPS):
        for j in range(DROP_RATE):
            dut.req_val.value = 1
            dut.req_msg.value = random.getrandbits(NUM_BITS)
            assert(dut.resp_msg.value == dut.req_msg.value)
            assert(dut.resp_val.value == 1)
            await ClockCycles(dut.clk, 1)
        
        

async def drop_test(dut, NUM_BITS, NUM_LOOPS, DROP_RATE):
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    
    
    dut.enable.value = 0
    
    dut.cfg_drop_val.value = 1
    dut.cfg_drop_msg.value = DROP_RATE
    await ClockCycles(dut.clk, 1)
    for i in range(NUM_LOOPS):
        dut.req_val.value = 1
        dut.req_msg.value = random.getrandbits(NUM_BITS)

        await ClockCycles(dut.clk, 1)
        assert dut.resp_val.value == 1

        assert dut.resp_msg.value == dut.req_msg.value
        for j in range(DROP_RATE-1):
            dut.req_val.value = 1
            dut.req_msg.value = random.getrandbits(NUM_BITS)
            await ClockCycles(dut.clk, 1)
            assert dut.resp_val.value == 0
        
        

@cocotb.test()
async def run_enable_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    random.seed(2)
    for i in range(100):
        await enable_basic_test_2(dut, 8, random.randint(1,25), random.randint(1,25))

@cocotb.test()
async def run_drop_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    random.seed(2)
    
    await drop_test(dut, 8, random.randint(1,25), random.randint(1,25))