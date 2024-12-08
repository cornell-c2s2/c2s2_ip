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
from lfsr_model import *

# Helper tasks -------------------------------------------------------------
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
            randnum = np.random.randint(0,2)
            req_msgs[i] += str(randnum)

    return req_msgs


# SEED (Int Array) --> Seed value.
async def lfsr_basic_test(dut, SEED, MODEL_OUTPUTS, num_outputs):

    # Reset
    dut.reset.value = 1

    #Start clock
    await ClockCycles(dut.clk, 1)

    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    '''
    TESTING FSM TRANSITIONS
    '''
    # Load LFSR - IDLE --> GEN_VAL
    dut.req_val.value = 1
    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '00'
    assert str(dut.next_state.value) == '01'
    
    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '01'
    
    dut.req_val.value = 0
    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '00'

    # GEN_VAL
    dut.req_val.value = 1

    binary_list = convert_binary_strings_to_lists(SEED)
    input_seed = binaryarray_to_binaryvalue(binary_list[0])
    dut.req_msg.value = input_seed
    dut.resp_rdy.value = 0

    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '00'
    assert str(dut.next_state.value) == '01'
    assert str(dut.load_Q.value) == '1'
     
    '''
    TESTING FOR SHIFTING
    GEN_VAL --> req_msg[31:0] loaded into Q
    '''
    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '01'
    assert str(dut.load_Q.value) == '0'
    #print("req_msg loaded: " + str(dut.req_msg.value))
    #print("Starting Q: " + str(dut.Q.value) + "\n")

    
    dut.resp_rdy.value = 1

    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '01'
    assert str(dut.next_state.value) == '10'

    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '10'
    assert str(dut.next_state.value) == '01'


    await ClockCycles(dut.clk, 1)

    
    
    for i in range(num_outputs):
        #print("||| SHIFT " + str(i) + " |||")

        #print("TAP: " + str(dut.final_tap.value))

        #print(str(dut.resp_msg.value))
        
        if(MODEL_OUTPUTS[0][i] == dut.resp_msg.value):
                #print("PASS. \n")
                assert True
        else:
            #print("Failing here: \n" + "MODEL OUTPUT: "  + str(MODEL_OUTPUTS[0][i]) + "\n" + "LFSR:         " +  str(dut.resp_msg.value) + "\n")
            assert False
        
        
        
        await ClockCycles(dut.clk, 1)
        await ClockCycles(dut.clk, 1)
    
    '''
    Testing Reset
    '''
    for i in range(10):
        val = np.random.randint(0,2)
        dut.reset.value = val
        await ClockCycles(dut.clk, 1)
        if(val == 1):
            assert dut.next_state.value == '00'

    '''
    req_val Coverage
    '''
    dut.reset.value = 0
    dut.resp_rdy.value = 0
    await ClockCycles(dut.clk, 1)


    for i in range(10):
        val = np.random.randint(0,2)
        dut.req_val.value = val
        await ClockCycles(dut.clk, 1)
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
    resp_rdy Coverage
    '''
    dut.reset.value = 0
    dut.req_val.value = 1
    await ClockCycles(dut.clk, 1)


    for i in range(10):
        val = np.random.randint(0,2)
        dut.resp_rdy.value = val
        await ClockCycles(dut.clk, 1)
        
        if(val == 1 and dut.state.value == '01'):
            assert dut.next_state.value == '10'
        elif(val == 0 and dut.state.value == '01'):
            assert dut.next_state.value == '01'
        

async def lfsr_Q_test(dut, SEED, MODEL_OUTPUTS, num_outputs):
     # Reset
    dut.reset.value = 1

    #Start clock
    await cocotb.start(generate_clock(dut))
    await ClockCycles(dut.clk, 1)

    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)
    
    for cycle in range(num_outputs):  # Increase this for broader coverage
        # Randomize inputs each cycle
        random.seed(0)
        dut.req_val.value = random.randint(0, 1)
        dut.resp_rdy.value = random.randint(0, 1)
        dut.reset.value = random.randint(0, 1)
        
        await ClockCycles(dut.clk, 1)

        # Check the FSM state and internal signals for expected behavior
        if dut.reset.value == 1:
            assert dut.next_state.value == dut.IDLE, "FSM should be in IDLE state on reset"
        
        if dut.state.value == dut.GEN_VAL:
            assert dut.req_rdy.value == 0 and dut.resp_val.value == 1, "GEN_VAL should set resp_val high"
        elif dut.state.value == dut.IDLE and dut.next_state.value == dut.GEN_VAL:
            assert dut.load_Q.value == 1

    
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == '00'
    
    dut.reset.value = 0
    
     # GEN_VAL
    dut.req_val.value = 1

    binary_list = convert_binary_strings_to_lists(SEED)
    input_seed = binaryarray_to_binaryvalue(binary_list[0])
    dut.req_msg.value = input_seed
    dut.resp_rdy.value = 0

    await ClockCycles(dut.clk, 1)
    assert str(dut.state.value) == '00'
    assert str(dut.next_state.value) == '01'
    assert str(dut.load_Q.value) == '1'
    
    await ClockCycles(dut.clk, 1)
    input_seed_1 = str(input_seed)
    assert str(dut.Q.value) == input_seed_1

    binary_list = convert_binary_strings_to_lists(SEED)
    num_range = len(binary_list)
    #print(num_range)
    for i in range(num_range):
        #print(i)
        dut.reset.value = 1
        await ClockCycles(dut.clk, 1)
        await ClockCycles(dut.clk, 1)
        assert dut.state.value == '00'
        
        dut.reset.value = 0
        
        # GEN_VAL
        dut.req_val.value = 1

        input_seed = binaryarray_to_binaryvalue(binary_list[i])
        dut.req_msg.value = input_seed
        dut.resp_rdy.value = 0

        await ClockCycles(dut.clk, 1)
        assert str(dut.state.value) == '00'
        assert str(dut.next_state.value) == '01'
        assert str(dut.load_Q.value) == '1'
        
        await ClockCycles(dut.clk, 1)
        input_seed_1 = str(input_seed)
        assert str(dut.Q.value) == input_seed_1

        await ClockCycles(dut.clk, 1)

    
async def lfsr_FSM_test(dut):
     # Reset
    dut.reset.value = 1

    #Start clock
    await cocotb.start(generate_clock(dut))
    await ClockCycles(dut.clk, 1)

    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

    # Initialize
    dut.reset.value = 1
    dut.req_val.value = 0
    dut.resp_rdy.value = 0
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)

    # Reset to IDLE state
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)
    
    # Transition IDLE -> GEN_VAL
    dut.req_val.value = 1
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.GEN_VAL, "FSM should transition to GEN_VAL on req_val"

    # Transition GEN_VAL -> RES_VAL
    dut.resp_rdy.value = 1
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.SEND_VAL

    # Transition SEND -> IDLE
    dut.req_val.value = 0
    dut.resp_rdy.value = 0
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.IDLE, "FSM should transition back to IDLE after resp_rdy"

    # Test FSM reset behavior from GEN_VAL state
    dut.req_val.value = 1
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.GEN_VAL, "FSM should be in GEN_VAL"

    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    await ClockCycles(dut.clk, 1)
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
