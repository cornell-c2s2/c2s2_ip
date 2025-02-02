import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge
from cocotb.clock import Clock
 
@cocotb.test()
async def my_first_test(dut):
    assert 1 == 1