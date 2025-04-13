import random

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

@cocotb.test()
async def basic_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)
    
    dut.enable.value = 0
    dut.cfg_drop_val.value = 0
    # dut.cfg_drop_msg.value = 5
    
    for i in range(5):
        for j in range(9):
            dut.req_val.value = 1
            dut.req_msg.value = j+1
            await ClockCycles(dut.clk, 1)
        dut.req_val.value = 1
        dut.req_msg.value = 10
        await ClockCycles(dut.clk, 1)

