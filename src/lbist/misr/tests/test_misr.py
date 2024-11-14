import pytest
import os
import random
import sys
import subprocess
from pathlib import Path
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb.binary import BinaryValue
import pdb

# Global Params ------------------------------------------------------------
NUM_RANDOM_TESTS = 5
TB_SEED = 0

# Helper tasks -------------------------------------------------------------
# Generate clock pulses
async def generate_clock(dut):
    while(1):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")


# Coverts binary array to cocotb.binary,BinaryValue
# Ex: [0, 1, 0, 1] ==> 0101
def binaryarray_to_binaryvalue(binary_list):
    binary_string = ''.join(str(bit) for bit in binary_list)
    return BinaryValue(binary_string)


# Generates an array of random positive integers with a maximum value of 4294967294.
# - size (int): The number of random integers to generate.
# - seed_value (int, optional): The seed for the random number generator.
def generate_random_array(size):
    max_value = 4294967294
    arr = [random.randint(1, max_value) for _ in range(size)]
    # print(arr)
    return arr


# CUT_OUTPUTS (Int Array) --> Things to hash into a signature
# OUTPUTS_TO_HASH (Int)   --> The number of inputs to hash
# SEED (Int Array)        --> Seed value.
async def misr_basic_test(dut, CUT_OUTPUTS, OUTPUTS_TO_HASH, SEED = [0] * 32):

    # Functional Model Output
    MODEL_OUTPUT = misr_model(CUT_OUTPUTS, SEED)

    # Reset
    dut.reset.value = 1

    #Start clock
    await RisingEdge(dut.clk)

    # Reset to 0
    dut.reset.value = 0
    await RisingEdge(dut.clk)

    # Load MISR with number of outputs it should expect to hash
    dut.lbist_req_val.value = 1
    dut.lbist_req_msg.value = OUTPUTS_TO_HASH
    dut.lbist_resp_rdy.value = 0

    # Zero message from CUT
    dut.cut_req_val.value = 0 
    dut.cut_req_msg.value = 0
    await RisingEdge(dut.clk)

    # Invalidate req message from lbist controller
    dut.lbist_req_val.value = 0

    # Feed values into MISR
    for i in range(len(CUT_OUTPUTS)):
        dut.cut_req_val.value = 1
        dut.cut_req_msg.value = CUT_OUTPUTS[i]
        await RisingEdge(dut.clk)

    dut.cut_req_val.value = 0
    while(dut.lbist_resp_val.value != 1):
        await RisingEdge(dut.clk)

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

    await RisingEdge(dut.clk)
    dut.lbist_resp_rdy.value = 1
    await RisingEdge(dut.clk)
    dut.lbist_resp_rdy.value = 0

    # RESET 
    dut.reset.value = 1
    await RisingEdge(dut.clk)
    dut.reset.value = 0


# Functional Model ---------------------------------------------------------
def misr_model(int_array, seed):
    signature = seed
    for num in int_array:
        # Convert integer to binary with the same length as the seed, then to a list of bits
        binary_entry = [int(bit) for bit in bin(num)[2:].zfill(len(seed))]

        # Do the xor
        for i in range(len(signature)):
            signature[i] = signature[i] ^ binary_entry[i]

        # Do the bitshift
        signature_msb = signature[0]
        for i in range(1, len(signature)):
            signature[i - 1] = signature[i]

        # Place the original MSB at the end
        signature[-1] = signature_msb
        # print(signature)

    return binaryarray_to_binaryvalue(signature)


# Tests --------------------------------------------------------------------
# Single directed test
@cocotb.test()
async def misr_basic_test1(dut):
    await cocotb.start(generate_clock(dut))
    CUT_OUTPUTS = [100, 2, 20, 2000, 2, 1, 3]
    OUTPUTS_TO_HASH = len(CUT_OUTPUTS)
    SEED = [0]*32
    await misr_basic_test(dut, CUT_OUTPUTS, OUTPUTS_TO_HASH, SEED)


# Single directed test
@cocotb.test()
async def misr_basic_test2(dut):
    await cocotb.start(generate_clock(dut))
    CUT_OUTPUTS = [7,1]
    OUTPUTS_TO_HASH = len(CUT_OUTPUTS)
    SEED = [0]*32
    await misr_basic_test(dut, CUT_OUTPUTS, OUTPUTS_TO_HASH, SEED)


# Random Tests
@cocotb.test()
async def misr_random_test(dut):
    await cocotb.start(generate_clock(dut))
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
        

