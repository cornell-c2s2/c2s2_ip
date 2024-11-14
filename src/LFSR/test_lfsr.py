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
    np.random.seed(98)
    num = np.random.rand(num_msgs) * 1000000000

    for i in range(num_msgs):
        req_msgs.append(bin(int(num[i]))) 
        req_msgs[i] = req_msgs[i][2:]
        
        while(len(req_msgs[i]) < 32):
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

    tap1 = XOR(int(Q6), int(Q31))
    tap2 = XOR(int(Q5), tap1)
    return XOR(int(Q1), tap2)


# Functional Model ---------------------------------------------------------
def lfsr_model(string_array, num_msgs, num_outputs):
    resq_msgs = []
    
    for i in range(num_msgs):
        
        Q = string_array[i]

        resq_msgs.append([])

        for j in range(num_outputs):
            resq_msgs[i].append(Q)
            #print("Model Taps: " + str(taps(Q)))
            Q = Q[1:] + str(taps(Q))

    final_resq_msgs = []

    for i in range(num_msgs):
        final_resq_msgs.append([])
        binarylist = convert_binary_strings_to_lists(resq_msgs[i])
        for array in binarylist:
            final_resq_msgs[i].append(binaryarray_to_binaryvalue(array))
    
    return final_resq_msgs


# SEED (Int Array)        --> Seed value.
async def lfsr_basic_test(dut, SEED, MODEL_OUTPUTS, num_outputs):

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
    #print("req_msg loaded: " + str(dut.req_msg.value))
    #print("Starting Q: " + str(dut.Q.value) + "\n")

    
    dut.resq_rdy.value = 1

    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '10'

    await RisingEdge(dut.clk)
    assert str(dut.state.value) == '10'
    assert str(dut.next_state.value) == '01'


    await RisingEdge(dut.clk)

    
    
    for i in range(num_outputs):
        #print("||| SHIFT " + str(i) + " |||")

        #print("TAP: " + str(dut.final_tap.value))

        #print(str(dut.resq_msg.value))
        
        if(MODEL_OUTPUTS[0][i] == dut.resq_msg.value):
                #print("PASS. \n")
                assert True
        else:
            #print("Failing here: \n" + "MODEL OUTPUT: "  + str(MODEL_OUTPUTS[0][i]) + "\n" + "LFSR:         " +  str(dut.resq_msg.value) + "\n")
            assert False
        
        
        
        await RisingEdge(dut.clk)
        await RisingEdge(dut.clk)
    
    '''
    Testing Reset
    '''
    for i in range(10):
        val = np.random.randint(0,2)
        dut.reset.value = val
        await RisingEdge(dut.clk)
        if(val == 1):
            assert dut.next_state.value == '00'

    '''
    req_val Coverage
    '''
    dut.reset.value = 0
    dut.resq_rdy.value = 0
    await RisingEdge(dut.clk)


    for i in range(10):
        val = np.random.randint(0,2)
        dut.req_val.value = val
        await RisingEdge(dut.clk)
        if(val == 1 and dut.state.value == '00'):
            assert dut.next_state.value == '01'
        elif(val == 0 and dut.state.value == '00'):
            assert dut.next_state.value == '00'
        elif(val == 1 and dut.state.value == '01'):
            assert dut.next_state.value == '01'
        elif(val == 0 and dut.state.value == '01'):
            assert dut.next_state.value == '00'
        elif(dut.state.value == '10'):
            assert dut.next_state.value == '01'

    '''
    resq_rdy Coverage
    '''
    dut.reset.value = 0
    dut.req_val.value = 1
    await RisingEdge(dut.clk)


    for i in range(10):
        val = np.random.randint(0,2)
        dut.resq_rdy.value = val
        await RisingEdge(dut.clk)
        
        if(val == 1 and dut.state.value == '01'):
            assert dut.next_state.value == '10'
        elif(val == 0 and dut.state.value == '01'):
            assert dut.next_state.value == '01'
        

async def lfsr_Q_test(dut, SEED, MODEL_OUTPUTS, num_outputs):
     # Reset
    dut.reset.value = 1

    #Start clock
    await cocotb.start(generate_clock(dut))
    await RisingEdge(dut.clk)

    # Reset to 0
    dut.reset.value = 0
    await RisingEdge(dut.clk)
    
    for cycle in range(num_outputs):  # Increase this for broader coverage
        # Randomize inputs each cycle
        random.seed(0)
        dut.req_val.value = random.randint(0, 1)
        dut.resq_rdy.value = random.randint(0, 1)
        dut.reset.value = random.randint(0, 1)
        
        await RisingEdge(dut.clk)

        # Check the FSM state and internal signals for expected behavior
        if dut.reset.value == 1:
            assert dut.next_state.value == dut.IDLE, "FSM should be in IDLE state on reset"
        
        if dut.state.value == dut.GEN_VAL:
            assert dut.req_rdy.value == 0 and dut.resq_val.value == 1, "GEN_VAL should set resq_val high"
        elif dut.state.value == dut.IDLE and dut.next_state.value == dut.GEN_VAL:
            assert dut.load_Q.value == 1

    
    await RisingEdge(dut.clk)
    dut.reset.value = 1
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    assert dut.state.value == '00'
    
    dut.reset.value = 0
    
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
    
    await RisingEdge(dut.clk)
    input_seed_1 = str(input_seed)
    assert str(dut.Q.value) == input_seed_1

    binary_list = convert_binary_strings_to_lists(SEED)
    num_range = len(binary_list)
    print(num_range)
    for i in range(num_range):
        print(i)
        dut.reset.value = 1
        await RisingEdge(dut.clk)
        await RisingEdge(dut.clk)
        assert dut.state.value == '00'
        
        dut.reset.value = 0
        
        # GEN_VAL
        dut.req_val.value = 1

        input_seed = binaryarray_to_binaryvalue(binary_list[i])
        dut.req_msg.value = input_seed
        dut.resq_rdy.value = 0

        await RisingEdge(dut.clk)
        assert str(dut.state.value) == '00'
        assert str(dut.next_state.value) == '01'
        assert str(dut.load_Q.value) == '1'
        
        await RisingEdge(dut.clk)
        input_seed_1 = str(input_seed)
        assert str(dut.Q.value) == input_seed_1

        await RisingEdge(dut.clk)

    
async def lfsr_FSM_test(dut):
     # Reset
    dut.reset.value = 1

    #Start clock
    await cocotb.start(generate_clock(dut))
    await RisingEdge(dut.clk)

    # Reset to 0
    dut.reset.value = 0
    await RisingEdge(dut.clk)

    # Initialize
    dut.reset.value = 1
    dut.req_val.value = 0
    dut.resq_rdy.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)

    # Reset to IDLE state
    dut.reset.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    
    # Transition IDLE -> GEN_VAL
    dut.req_val.value = 1
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    assert dut.state.value == dut.GEN_VAL, "FSM should transition to GEN_VAL on req_val"

    # Transition GEN_VAL -> RES_VAL
    dut.resq_rdy.value = 1
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    assert dut.state.value == dut.SEND_VAL

    # Transition SEND -> IDLE
    dut.req_val.value = 0
    dut.resq_rdy.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    assert dut.state.value == dut.IDLE, "FSM should transition back to IDLE after resq_rdy"

    # Test FSM reset behavior from GEN_VAL state
    dut.req_val.value = 1
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    assert dut.state.value == dut.GEN_VAL, "FSM should be in GEN_VAL"

    dut.reset.value = 1
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    assert dut.state.value == dut.IDLE, "FSM should return to IDLE on reset"



@cocotb.test()
async def test(dut):
    NUM_MSGS = 1 # do not change 
    REQ_MSGS = generate_seeds(NUM_MSGS)

    MODEL_OUTPUT = lfsr_model(REQ_MSGS, NUM_MSGS, 1000)
    #print("Model Output: " + str(MODEL_OUTPUT))
    await lfsr_basic_test(dut, REQ_MSGS, MODEL_OUTPUT, 1000)


@cocotb.test()
async def test1(dut):
    NUM_MSGS = 1 # do not change 
    REQ_MSGS = generate_seeds(NUM_MSGS)
    MODEL_OUTPUT = lfsr_model(REQ_MSGS, NUM_MSGS, 100)
    print("2ND TEST!")
    SEED_MSGS = 1000
    SEED_MSGS = generate_seeds(SEED_MSGS)
    await lfsr_Q_test(dut, SEED_MSGS, MODEL_OUTPUT, 100)

@cocotb.test()
async def test2(dut):
    print("3rd")
    await lfsr_FSM_test(dut)

