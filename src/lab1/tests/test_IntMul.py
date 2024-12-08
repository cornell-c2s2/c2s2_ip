#Cocotb imports
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
from pymtl3 import *

#Model parameters
bits = int(os.getenv("N", 32))
decimal = int(os.getenv("D", 16))

#Check if expected value of c is the same as the actual value
def equal(actual, expected):
    #To account for underflow discrepancy
    return actual == expected or actual == expected-1

def mk_imsg( a, b ):
  value = concat( Bits32( a, trunc_int=True ), Bits32( b, trunc_int=True ) )
  return int(value)
  
#Reset then multiply coroutine
async def reset_then_mult(dut, a, b): 
    #Set initial values of signals
    dut.istream_msg.value = mk_imsg(a, b)
    dut.reset.value = 1
    dut.istream_val.value = 0
    dut.ostream_rdy.value = 0
    await ClockCycles(dut.clk, 1)

    #End reset and spend whole cycle in IDLE state
    dut.reset.value = 0
    await ClockCycles(dut.clk, 2)

    #Send valid request signal to the multiplier and wait for a valid response
    dut.istream_val.value = 1
    await RisingEdge(dut.ostream_val)

    #Acknowledge the valid response
    dut.ostream_rdy.value = 1
    dut.istream_val.value = 0
    await ClockCycles(dut.clk, 1)
    
#Single directed test
@cocotb.test()
async def multiplier_basic_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    #Reset multiplier then multiply inputs
    A = 15
    B = 13
    await reset_then_mult(dut, A, B)

    #Check the value returned by the multiplier
    C = A*B

    assert equal(int(dut.ostream_msg.value), C), "C not correct" 

@cocotb.test()
async def multiplier_randomized_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    for i in range(1000):
        #Reset multiplier then multiply inputs
        A = random.randint(-(2**31), (2**31)-1)
        B = random.randint(-(2**31), (2**31)-1)
        await reset_then_mult(dut, A, B)

        #Check the value returned by the multiplier
        C = A*B
        C = C % (2**32)

        assert equal(int(dut.ostream_msg.value), C), "C not correct" 
