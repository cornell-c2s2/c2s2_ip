import os
import random
import sys
import subprocess
from pathlib import Path

import cocotb
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb.runner import get_runner

#Generate clock pulses (50 cycles)
async def generate_clock(dut):
    for cycle in range(50):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

def update_control(dut, counter):
    if (counter == 31):
        dut.do_carry.value = 1
    else:
        dut.do_carry.value = 0   

#Single directed test
@cocotb.test()
async def datapath_basic_test(dut):
    #Set initial values of signals
    dut.a.value = 15
    dut.b.value = 13
    dut.in_wait.value = 1
    dut.reset.value = 1
    dut.do_add.value = 0
    dut.do_carry.value = 0
    
    #Start clock
    await cocotb.start(generate_clock(dut))
    await RisingEdge(dut.clk)
    #Start the operation of the control path model
    dut.reset.value = 0
    dut.do_add.value = 1
    await RisingEdge(dut.clk)
    dut.in_wait.value = 0
    await FallingEdge(dut.clk)
    for x in range(32):
        await RisingEdge(dut.clk)
        update_control(dut, x)
        await FallingEdge(dut.clk)

    #Check the value returned by the datapath
    assert int(dut.c.value) == 195, "C not equal to 195"

@cocotb.test()
async def datapath_reset_test(dut):
    pass

@cocotb.test()
async def datapath_randomised_test(dut):
    pass

def test_datapath_runner():
    """Simulate the multiplier datapath using the Python runner.

        This file can be run directly or via pytest discovery.
    """
    sim = os.getenv("SIM", "icarus")

    proj_path = Path(__file__).resolve().parent.parent.parent.parent

    #equivalent to setting the PYTHONPATH environment variable
    sys.path.append(str(proj_path / "fixed_point" / "iterative" / "test_cocotb"))

    #1) Preprocess Verilog code using Icarus Verilog

    #2) Set verilog source with Preprocessed file (do not need includes)
    sources = [
       proj_path / "fixed_point" / "iterative" / "multiplier.v"
    ] 

    includes = [
        proj_path
    ]
  
    #3)Set build and test arguments
    build_args = ["-s", "FXPIterMultDatapath"]
    test_args = []

    #4) Instantiate runner (no includes necessary)
    runner = get_runner(sim)
    runner.build(
        verilog_sources=sources,
        includes=includes,
        hdl_toplevel="FXPIterMultDatapath",
        always=True,
        build_args=build_args
    )

    runner.test(
        hdl_toplevel="FXPIterMultDatapath", test_module="test_FXPIterMultDatapath", waves=True,test_args=test_args
    )


if __name__ == "__main__":
    test_datapath_runner()