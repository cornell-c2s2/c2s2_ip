import random

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock



# Tests PosedgeDetector's basic functionality
@cocotb.test()
async def basic_PosedgeDetector_test1(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    # Reset to 1
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    
    # Reset to 0
    dut.reset.value = 0
    dut.req_val = 0
    await ClockCycles(dut.clk, 1)

    # Set req_val high
    dut.req_val = 1
    await ClockCycles(dut.clk, 1)

    # resp_val high in same cycle
    assert dut.resp_val == 1
    await ClockCycles(dut.clk, 1)

    # resp_val no longer high even though req_val is still asserted
    assert dut.resp_val == 0


# Tests PosedgeDetector's basic functionality
@cocotb.test()
async def basic_PosedgeDetector_test2(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    # Reset to 1
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    
    # Reset to 0
    dut.reset.value = 0
    dut.req_val = 0
    await ClockCycles(dut.clk, 1)

    # Set req_val high
    dut.req_val = 1
    await ClockCycles(dut.clk, 1)

    # resp_val high in same cycle
    assert dut.resp_val == 1
    await ClockCycles(dut.clk, 1)

    # resp_val no longer high even though req_val is still asserted
    assert dut.resp_val == 0
    # Deassert req_val
    dut.req_val = 0
    await ClockCycles(dut.clk, 1)

    # assert req_val
    dut.req_val = 1
    await ClockCycles(dut.clk, 1)

    # resp_val high in same cycle
    assert dut.resp_val == 1
    await ClockCycles(dut.clk, 1)

    # resp_val no longer high even though req_val is still asserted
    assert dut.resp_val == 0
