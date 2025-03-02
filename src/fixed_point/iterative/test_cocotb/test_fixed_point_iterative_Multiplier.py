#Cocotb imports
import pytest
import cocotb
import os
import sys
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.runner import get_runner
from cocotb.clock import Clock
from pathlib import Path

#Util imports
from fxpmath.objects import Fxp
import random

#Model parameters
bits = int(os.getenv("N", 32))
decimal = int(os.getenv("D", 16))

#Check if expected value of c is the same as the actual value
def equal(actual, expected):
    #To account for underflow discrepancy
    return actual == expected or actual == expected-1

#Reset then multiply coroutine
async def reset_then_mult(dut, n, d, a, b): 
    #Set initial values of signals
    A = Fxp(a, signed=True, n_word=n, n_frac=d, rounding='around')
    B = Fxp(b, signed=True, n_word=n, n_frac=d, rounding='around')
    dut.a.value = int(A.bin(), 2)
    dut.b.value = int(B.bin(), 2)
    dut.reset.value = 1
    dut.recv_val.value = 0
    dut.send_rdy.value = 0
    await ClockCycles(dut.clk, 1)

    #End reset and spend whole cycle in IDLE state
    dut.reset.value = 0
    await ClockCycles(dut.clk, 2)

    #Send valid request signal to the multiplier and wait for a valid response
    dut.recv_val.value = 1
    await RisingEdge(dut.send_val)

    #Acknowledge the valid response
    dut.send_rdy.value = 1
    dut.recv_val.value = 0
    await ClockCycles(dut.clk, 1)
    

#Single directed test
@cocotb.test()
async def multiplier_basic_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    #Reset multiplier then multiply inputs
    A = 5.37232
    B = 4.7883
    await reset_then_mult(dut, bits, decimal, A, B)

    #Check the value returned by the multiplier
    C = Fxp(A, signed=True, n_word=bits, n_frac=decimal, rounding='around')*Fxp(B, signed=True, n_word=bits, n_frac=decimal, rounding='around')
    C.resize(n_word=bits, n_frac=decimal)
    assert equal(int(dut.c.value), int(C.bin(), 2)), "C not correct" 

async def multiplier_randomized_test(dut, n, d):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    for i in range(1000):
        #Reset multiplier then multiply inputs
        A = random.uniform(-300, 300)
        B = random.uniform(-300, 300)
        await reset_then_mult(dut, n, d, A, B)

        #Check the value returned by the multiplier
        C = Fxp(A, signed=True, n_word=n, n_frac=d, rounding='around')*Fxp(B, signed=True, n_word=n, n_frac=d, rounding='around')
        C.resize(n_word=n, n_frac=d)

        #Check for overflow
        overflow = A*B > 2**(n-d-1) or A*B < -2**(n-d-1)

        assert equal(int(dut.c.value), int(C.bin(), 2)) or overflow, "C not correct" 

#Creation of test factories for parameter combinations
@cocotb.test()
async def multiplier_randomized_test_wrapper(dut):
    await multiplier_randomized_test(dut, bits, decimal)

def test_multiplier_runner():
    sim = os.getenv("SIM", "verilator")

    proj_path = Path(__file__).resolve().parent.parent

    sources = [proj_path / "multiplier.v"]
    includes =[proj_path / ".." / ".."]

    # equivalent to setting the PYTHONPATH environment variable
    sys.path.append(str(proj_path / "test_cocotb"))

    runner = get_runner(sim)
    runner.build(
        verilog_sources=sources,
        hdl_toplevel="fixed_point_iterative_Multiplier",
        always=True,
        includes= includes,
        build_args=[],
    )
    runner.test(
        hdl_toplevel="fixed_point_iterative_Multiplier", test_module="test_fixed_point_iterative_Multiplier", test_args=[]
    )


if __name__ == "__main__":
    test_multiplier_runner()