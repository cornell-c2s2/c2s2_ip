#Cocotb imports
import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.runner import get_runner
from cocotb.clock import Clock

#Util imports
from fxpmath.objects import Fxp
import random

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
    await reset_then_mult(dut, A, B)

    #Check the value returned by the multiplier
    C = Fxp(A, signed=True, n_word=32, n_frac=16, rounding='around')*Fxp(B, signed=True, n_word=32, n_frac=16, rounding='around')
    C.resize(n_word=32, n_frac=16)
    assert equal(int(dut.c.value), int(C.bin(), 2)), "C not correct" 

@cocotb.test()
async def multiplier_randomized_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
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
