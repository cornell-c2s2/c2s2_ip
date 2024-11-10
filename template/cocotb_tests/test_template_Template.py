import random

import cocotb
from cocotb.triggers import Timer, RisingEdge  # also has FallingEdge, etc.

async def generate_clock(dut):
    while True:
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

@cocotb.test()
async def basic_test(dut):
    await cocotb.start(generate_clock(dut))
    dut.reset.value = 1
    await RisingEdge(dut.clk)
    dut.reset.value = 0

    dut.recv_msg.value = 1
    await RisingEdge(dut.clk)
    dut._log.info("Hello world!")
    assert dut.send_msg.value == dut.recv_msg.value

@cocotb.test()
async def randomized_test(dut):
    await cocotb.start(generate_clock(dut))
    dut.reset.value = 1
    await RisingEdge(dut.clk)
    dut.reset.value = 0

    for i in range(100):
        a = random.randint(0, 2 ** 32 - 1)
        dut.recv_msg.value = a
        assert dut.send_msg.value == dut.recv_msg.value
        await RisingEdge(dut.clk)
    

    