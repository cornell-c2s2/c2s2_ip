import os
import random
import sys
import subprocess
from pathlib import Path

import cocotb
from fxpmath.objects import Fxp
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
        dut.do_carry.value = dut.do_carry.value   

#Single directed test
@cocotb.test()
async def datapath_basic_test(dut):
    #Set initial values of signals
    A = Fxp(-5.25, signed=True, n_word=48, n_frac=16)
    B = Fxp(3.75, signed=True, n_word=32, n_frac=16)
    dut.a.value = int(A.bin(), 2)
    dut.b.value = int(B.bin(), 2)
    dut.in_wait.value = 1
    dut.reset.value = 1
    dut.do_add.value = 0
    dut.do_carry.value = 0

    #Start clock
    await cocotb.start(generate_clock(dut))
    await RisingEdge(dut.clk)
    #End reset
    dut.reset.value = 0
    await RisingEdge(dut.clk)
    #Start 
    dut.do_add.value = 1
    dut.in_wait.value = 0
    await FallingEdge(dut.clk)
    for x in range(32):
        update_control(dut, x)
        await RisingEdge(dut.clk)
        await FallingEdge(dut.clk)
    #Check the value returned by the datapath
    C = Fxp(-5.25*3.75, signed=True, n_word=32, n_frac=16)
    assert dut.c.value == int(C.bin(),2), "C not equal to 195"

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