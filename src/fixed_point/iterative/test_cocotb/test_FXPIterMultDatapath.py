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
from cocotb.binary import BinaryValue

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

#Updating the state of the multiplier
def update_control(dut, counter):
    if (counter == 31):
        dut.do_carry.value = 1
    elif (counter == 32): #Transition from CALC to DONE
        dut.do_add.value = 0
        dut.do_carry.value = 0 

#Reset then multiply coroutine (model for control path)
async def reset_then_mult(dut, a, b): 
    #Set initial values of signals
    A = Fxp(a, signed=True, n_word=32, n_frac=16, rounding='around')
    A.resize(n_word=48, n_frac=16)
    B = Fxp(b, signed=True, n_word=32, n_frac=16, rounding='around')
    dut.a.value = int(A.bin(), 2)
    dut.b.value = int(B.bin(), 2)
    dut.in_wait.value = BinaryValue("x")
    dut.reset.value = 1
    dut.do_add.value = 0
    dut.do_carry.value = 0

    #Start clock
    await cocotb.start(generate_clock(dut))
    await RisingEdge(dut.clk)

    #End reset and spend whole cycle in IDLE
    dut.reset.value = 0
    await RisingEdge(dut.clk)
    dut.in_wait.value = 1
    await RisingEdge(dut.clk)
    #Transition from IDLE to CALC
    dut.do_add.value = 1
    dut.in_wait.value = 0
    update_control(dut, 0)
    await RisingEdge(dut.clk)
    #Remain in CALC for 32 cycles then transition to DONE
    for x in range(1,33):
        update_control(dut, x)
        await RisingEdge(dut.clk)

#Single directed test
@cocotb.test()
async def datapath_basic_test(dut):
    #Reset multiplier then multiply inputs
    A = 5.37232
    B = 4.7883
    await reset_then_mult(dut, A, B)

    #Check the value returned by the datapath
    C = Fxp(A, signed=True, n_word=48, n_frac=16, rounding='around')*Fxp(B, signed=True, n_word=32, n_frac=16, rounding='around')
    C.resize(n_word=32, n_frac=16)
    assert equal(int(dut.c.value), int(C.bin(), 2)), "C not correct" 

@cocotb.test()
async def datapath_randomized_test(dut):
    for i in range(1000):
        #Reset multiplier then multiply inputs
        A = random.uniform(-300, 300)
        B = random.uniform(-300, 300)
        await reset_then_mult(dut, A, B)

        #Check the value returned by the datapath
        C = Fxp(A, signed=True, n_word=48, n_frac=16, rounding='around')*Fxp(B, signed=True, n_word=32, n_frac=16, rounding='around')
        C.resize(n_word=32, n_frac=16)

        #Check for overflow
        overflow = A*B > 32768 or A*B < -32768

        assert equal(int(dut.c.value), int(C.bin(), 2)) or overflow, "C not correct" 

def test_multiplier_datapath_runner():
    sim = os.getenv("SIM", "verilator")

    proj_path = Path(__file__).resolve().parent.parent

    sources = [proj_path / "multiplier.v"]
    includes =[proj_path / ".." / ".."]

    # equivalent to setting the PYTHONPATH environment variable
    sys.path.append(str(proj_path / "test_cocotb"))

    runner = get_runner(sim)
    runner.build(
        verilog_sources=sources,
        hdl_toplevel="FXPIterMultDatapath",
        always=True,
        includes= includes,
        build_args=[],
        waves = True
    )
    runner.test(
        hdl_toplevel="FXPIterMultDatapath", test_module="test_FXPIterMultDatapath", test_args=[], waves = True
    )


if __name__ == "__main__":
    test_multiplier_datapath_runner()