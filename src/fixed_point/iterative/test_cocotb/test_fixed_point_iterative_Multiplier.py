import pytest

import os
import random
import sys
import subprocess
from pathlib import Path

import cocotb
from fxpmath.objects import Fxp
from cocotb.triggers import Timer, RisingEdge
from cocotb.runner import get_runner

#Generate clock pulses (50 cycles)
async def generate_clock(dut):
    for cycle in range(50):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

#Check if expected value of c is the same as the actual value
def equal(actual, expected):
    #To account for underflow discrepancy
    return actual == expected or actual == expected-1

#Reset then multiply coroutine
async def reset_then_mult(dut, a, b): 
    #Set initial values of signals
    A = Fxp(a, signed=True, n_word=32, n_frac=16, rounding='around')
    B = Fxp(b, signed=True, n_word=32, n_frac=16, rounding='around')
    dut.a.value = int(A.bin(), 2)
    dut.b.value = int(B.bin(), 2)
    dut.reset.value = 1
    dut.recv_val.value = 0
    dut.send_rdy.value = 0

    #Start clock
    await cocotb.start(generate_clock(dut))
    await RisingEdge(dut.clk)

    #End reset and spend whole cycle in IDLE state
    dut.reset.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)

    #Send valid request signal to the multiplier and wait for a valid response
    dut.recv_val.value = 1
    await RisingEdge(dut.send_val)

    #Acknowledge the valid response
    dut.send_rdy.value = 1
    dut.recv_val.value = 0
    await RisingEdge(dut.clk)
    

#Single directed test
@cocotb.test()
async def multiplier_basic_test(dut):
    #Reset multiplier then multiply inputs
    A = 5.37232
    B = 4.7883
    await reset_then_mult(dut, A, B)

    #Check the value returned by the multiplier
    C = Fxp(A, signed=True, n_word=32, n_frac=16, rounding='around')*Fxp(B, signed=True, n_word=32, n_frac=16, rounding='around')
    C.resize(n_word=32, n_frac=16)
    assert equal(int(dut.c.value), int(C.bin(), 2)), "C not correct" 

@cocotb.test()
async def multiplier_reset_test(dut):
    #Initialize signal values

    #Reset

    #End reset

    #Run multiplication coroutine for a few cycles

    #Reset again

    #Check if values are correct

    #End reset
    pass

@cocotb.test()
async def multiplier_randomized_test(dut):
    for i in range(1000):
        #Reset multiplier then multiply inputs
        A = random.uniform(-300, 300)
        B = random.uniform(-300, 300)
        await reset_then_mult(dut, A, B)

        #Check the value returned by the multiplier
        C = Fxp(A, signed=True, n_word=32, n_frac=16, rounding='around')*Fxp(B, signed=True, n_word=32, n_frac=16, rounding='around')
        C.resize(n_word=32, n_frac=16)

        #Check for overflow
        overflow = A*B > 32768 or A*B < -32768

        assert equal(int(dut.c.value), int(C.bin(), 2)) or overflow, "C not correct" 

def test_multiplier_runner():
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
    build_args = []
    test_args = []

    #4) Instantiate runner (no includes necessary)
    runner = get_runner(sim)
    runner.build(
        verilog_sources=sources,
        includes=includes,
        hdl_toplevel="fixed_point_iterative_Multiplier",
        always=True,
        build_args=build_args
    )

    runner.test(
        hdl_toplevel="fixed_point_iterative_Multiplier", test_module="test_fixed_point_iterative_Multiplier", waves=True,test_args=test_args
    )


if __name__ == "__main__":
    test_multiplier_runner()