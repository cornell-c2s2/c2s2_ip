import pytest
import os
import random
import sys
import subprocess
from pathlib import Path
import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.binary import BinaryValue
import pdb
from misr_model import *

# Global Params ------------------------------------------------------------
NUM_RANDOM_TESTS = 10
TB_SEED = 0

# Helper tasks -------------------------------------------------------------
# CUT_OUTPUTS (Int Array) --> Things to hash into a signature
# OUTPUTS_TO_HASH (Int)   --> The number of inputs to hash
# SEED (Int Array)        --> Seed value.
async def misr_basic_test(dut, CUT_OUTPUTS, OUTPUTS_TO_HASH, SEED = [0] * 32):

    # Functional Model Output
    MODEL_OUTPUT = misr_model(CUT_OUTPUTS, SEED)

    # Start the clock
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    # Reset
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    

    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    # Load MISR with number of outputs it should expect to hash
    dut.lbist_req_val.value = 1
    dut.lbist_req_msg.value = OUTPUTS_TO_HASH
    dut.lbist_resp_rdy.value = 0

    # Zero message from CUT
    dut.cut_req_val.value = 0 
    dut.cut_req_msg.value = 0
    await ClockCycles(dut.clk, 1)

    # Invalidate req message from lbist controller
    dut.lbist_req_val.value = 0
    await ClockCycles(dut.clk, 1)

    # Feed values into MISR
    for i in range(len(CUT_OUTPUTS)):
        dut.cut_req_val.value = 1
        dut.cut_req_msg.value = CUT_OUTPUTS[i]
        await ClockCycles(dut.clk, 1)
        
    # Deassert cut_req_val 
    dut.cut_req_val.value = 0
    await ClockCycles(dut.clk, 1)

    # Wait for valid MISR output
    while(dut.lbist_resp_val.value != 1):
        await ClockCycles(dut.clk, 1)

    if( MODEL_OUTPUT == dut.lbist_resp_msg.value and dut.lbist_resp_val.value == 1):
        assert True
    else:
        dut._log.info("DUT OUTPUT")
        dut._log.info(dut.lbist_resp_msg.value)
        dut._log.info("MODEL OUTPUT")
        dut._log.info(MODEL_OUTPUT)
        dut._log.info(dut.lbist_resp_val.value)
        assert False
    
    # dut._log.info("DUT OUTPUT")
    # dut._log.info(dut.lbist_resp_msg.value)

    await ClockCycles(dut.clk, 1)
    dut.lbist_resp_rdy.value = 1
    await ClockCycles(dut.clk, 1)
    dut.lbist_resp_rdy.value = 0

    # RESET 
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0


# Tests --------------------------------------------------------------------
# Single directed test
@cocotb.test()
async def misr_basic_test1(dut):
    # await cocotb.start(generate_clock(dut))
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    CUT_OUTPUTS = [100, 2, 20, 2000, 2, 1, 3]
    OUTPUTS_TO_HASH = len(CUT_OUTPUTS)
    SEED = [0]*32
    await misr_basic_test(dut, CUT_OUTPUTS, OUTPUTS_TO_HASH, SEED)


# Single directed test
@cocotb.test()
async def misr_basic_test2(dut):
    # await cocotb.start(generate_clock(dut))
    CUT_OUTPUTS = [7,1]
    OUTPUTS_TO_HASH = len(CUT_OUTPUTS)
    SEED = [0]*32
    await misr_basic_test(dut, CUT_OUTPUTS, OUTPUTS_TO_HASH, SEED)


# Random Tests
@cocotb.test()
async def misr_random_test(dut):
    # await cocotb.start(generate_clock(dut))
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    aliasing_percentage = 0
    seen_signatures = {}
    for i in range(NUM_RANDOM_TESTS):
        # CUT_OUTPUTS = generate_random_array(random.randint(2, 31))
        CUT_OUTPUTS = generate_random_array(31)
        OUTPUTS_TO_HASH = len(CUT_OUTPUTS)
        SEED = [0]*32
        await misr_basic_test(dut, CUT_OUTPUTS, OUTPUTS_TO_HASH, SEED)

        # Calculate the aliasing percentage
        generated_signature = str(misr_model(CUT_OUTPUTS, SEED))
        if(generated_signature in seen_signatures):
            aliasing_percentage += 1
        else:
            seen_signatures[generated_signature] = 1
    
    dut._log.info("ALIASING_PERCENTAGE: " + str(100*(aliasing_percentage/(NUM_RANDOM_TESTS))))
        

