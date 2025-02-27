import random

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock



# Tests FifoPackager's basic functionality
# Cycle 1: send in 001
# Cycle 2: send in 010
# Cycle 3: output 010001
@cocotb.test()
async def basic_FifoPackager_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    # Reset to 1
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    
    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    # Send in 1
    dut.req_val.value = 1
    dut.req_msg.value = 1
    dut.resp_rdy.value = 0
    assert dut.req_rdy.value == 1
    await ClockCycles(dut.clk, 1)

    # Send in 2
    dut.req_val.value = 1
    dut.req_msg.value = 2
    assert dut.req_rdy.value == 1
    await ClockCycles(dut.clk, 1)

    # Clock cycle to generate output
    dut.resp_rdy.value = 1
    dut.req_val.value = 0
    await ClockCycles(dut.clk, 1)

    # Data should be ready here...
    dut._log.info("DUT OUTPUT")
    dut._log.info(str(dut.resp_msg.value))
    dut._log.info(str(dut.out.value))
    assert dut.req_rdy.value == 0
    
    # Setting resp_rdy high!
    assert dut.resp_val == 1
    await ClockCycles(dut.clk, 1)

    # Now, dut should be ready to service new request!
    await ClockCycles(dut.clk, 1)
    assert dut.req_rdy == 1


@cocotb.test()
async def FifoPackager_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    # Reset to 1
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    
    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    # Send in 1
    dut.req_val.value = 1
    dut.req_msg.value = 1
    dut.resp_rdy.value = 0
    assert dut.req_rdy.value == 1
    await ClockCycles(dut.clk, 1)

    # Set req_val low and insert delay
    dut.req_val.value = 0
    await ClockCycles(dut.clk, 1)
    DELAY = 5
    prev_counter = dut.counter.value
    for _ in range(DELAY):
        assert dut.req_rdy.value == 1
        assert dut.counter.value == prev_counter
        assert dut.resp_val.value == 0
        await ClockCycles(dut.clk, 1)
    
    dut._log.info(f"COUNTER:{prev_counter}")

    # Send in 2
    dut.req_val.value = 1
    dut.req_msg.value = 2
    assert dut.req_rdy.value == 1
    await ClockCycles(dut.clk, 1)

    # Clock cycle to generate output
    dut.resp_rdy.value = 1
    dut.req_val.value = 0
    await ClockCycles(dut.clk, 1)

    # Data should be ready here...
    dut._log.info("DUT OUTPUT")
    dut._log.info(str(dut.resp_msg.value))
    dut._log.info(str(dut.out.value))
    assert dut.req_rdy.value == 0
    
    # Setting resp_rdy high!
    assert dut.resp_val == 1
    await ClockCycles(dut.clk, 1)

    # Now, dut should be ready to service new request!
    await ClockCycles(dut.clk, 1)
    assert dut.req_rdy == 1
