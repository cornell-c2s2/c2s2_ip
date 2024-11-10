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

    dut.recv_msg.value = 1
    await ClockCycles(dut.clk, 1)
    dut._log.info("Hello world!")
    assert dut.send_msg.value == dut.recv_msg.value

@cocotb.test()
async def randomized_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0

    for i in range(100):
        dut.recv_msg.value = random.randint(0, 2 ** 20 - 1)
        dut._log.info(f"a_{i} = {hex(dut.recv_msg.value)}")
        assert dut.send_msg.value == dut.recv_msg.value
        await ClockCycles(dut.clk, 1)
    

    