# Imports needed by cocotb
import pytest
import os
import random
import sys
import subprocess
from pathlib import Path
import cocotb
import numpy as np
from cocotb.triggers import Timer, RisingEdge
from cocotb.runner import get_runner
from cocotb.binary import BinaryValue

import pdb

# Helper tasks -------------------------------------------------------------

#Generate clock pulses
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

# Converts ['101', '001', '111'] to  [[1, 0, 1], [0, 0, 1], [1, 1, 1]]
def convert_binary_strings_to_lists(binary_strings):
    return [[int(bit) for bit in binary_string] for binary_string in binary_strings]

#Generates one BIST seed
#BIST seeds generated (32 bits)
def generate_seeds(num_msgs):
    req_msgs = []
    num = np.random.rand(num_msgs) * 1000000000

    for i in range(num_msgs):
        req_msgs.append(bin(int(num[i]))) 
        req_msgs[i] = req_msgs[i][2:]
        
        while(len(req_msgs[i]) <= 37):
            req_msgs[i] += '0'
    
    return req_msgs

def XOR(a,b):
    if(int(a) == 0 and int(b) == 1):
        return 1
    elif(int(a) == 1 and int(b) == 0):
        return 1
    else:
        return 0

def taps(Q):
    #since Q is a str, need to do this backwards
    Q1 = Q[30:31]
    Q5 = Q[26:27]
    Q6 = Q[25:26]
    Q31 = Q[0:1]

    tap1 = XOR(int(Q1), int(Q5))
    tap2 = XOR(int(Q6), int(Q31))
    return XOR(tap1, tap2)


# Functional Model ---------------------------------------------------------
def lfsr_model(string_array, num_msgs):
    resq_msgs = []
    
    for i in range(num_msgs):
        
        Q = string_array[i]
        Q = Q[6:39]

        resq_msgs.append([])

        for j in range(5):
            resq_msgs[i].append(Q)
            print("Model Taps: " + str(taps(Q)))
            Q = Q[1:] + str(taps(Q))

    final_resq_msgs = []

    for i in range(num_msgs):
        final_resq_msgs.append([])
        binarylist = convert_binary_strings_to_lists(resq_msgs[i])
        for array in binarylist:
            final_resq_msgs[i].append(binaryarray_to_binaryvalue(array))
    
    return final_resq_msgs


# SEED (Int Array)        --> Seed value.
async def lfsr_basic_test(dut, SEED, MODEL_OUTPUTS):

    # Reset
    dut.reset.value = 1

    #Start clock
    await cocotb.start(generate_clock(dut))
    await RisingEdge(dut.clk)

    # Reset to 0
    dut.reset.value = 0
    await RisingEdge(dut.clk)

    '''
    TESTING FSM TRANSITIONS
    '''
    # Load LFSR - IDLE --> GEN_VAL
    dut.req_val.value = 1
    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '00'
    assert str(dut.next_state.value) == '01'
    
    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '01'
    
    dut.req_val.value = 0
    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '00'

    # GEN_VAL
    dut.req_val.value = 1

    binary_list = convert_binary_strings_to_lists(SEED)
    input_seed = binaryarray_to_binaryvalue(binary_list[0])
    dut.req_msg.value = input_seed
    dut.resq_rdy.value = 0

    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '00'
    assert str(dut.next_state.value) == '01'
    assert str(dut.load_Q.value) == '1'
     
    '''
    TESTING FOR SHIFTING
    GEN_VAL --> req_msg[31:0] loaded into Q
    '''
    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '01'
    assert str(dut.load_Q.value) == '0'
    print("req_msg loaded: " + str(dut.req_msg.value))
    print("Starting Q: " + str(dut.Q.value) + "\n")

    
    dut.resq_rdy.value = 1

    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '10'

    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '10'
    assert str(dut.next_state.value) == '01'
    assert str(dut.counter.value) == '000'


    await RisingEdge(dut.clk)

    
    
    for i in range(5):
        print("||| SHIFT " + str(i) + " |||")

        print("TAP: " + str(dut.final_tap.value))

        print(str(dut.resq_msg.value))
        
        if(MODEL_OUTPUTS[0][i] == dut.resq_msg.value):
                print("PASS. \n")
                assert True
        else:
            print("Failing here: \n" + "MODEL OUTPUT: "  + str(MODEL_OUTPUTS[0][i]) + "\n" + "LFSR:         " +  str(dut.resq_msg.value) + "\n")
            assert False
        
        
        
        await RisingEdge(dut.clk)
        await RisingEdge(dut.clk)
        
    
@cocotb.test()
async def test(dut):
    NUM_MSGS = 1 # do not change 
    REQ_MSGS = generate_seeds(NUM_MSGS)

    MODEL_OUTPUT = lfsr_model(REQ_MSGS, NUM_MSGS)
    print("Model Output: " + str(MODEL_OUTPUT))
    await lfsr_basic_test(dut, REQ_MSGS, MODEL_OUTPUT)
