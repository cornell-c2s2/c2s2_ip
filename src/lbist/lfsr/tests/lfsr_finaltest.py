
# Imports needed by cocotb
import pytest
import os
import random
import sys
import subprocess
from pathlib import Path
import cocotb
import numpy as np
from cocotb.triggers import Timer, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
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


# Generates num_seeds amount of seeds with BIT_WIDTH
def generate_seeds(num_seeds, BIT_WIDTH):
    req_msgs = []
    np.random.seed(98)
    num = np.random.rand(num_seeds) * 1000000000

    for i in range(num_seeds):
        req_msgs.append(bin(int(num[i]))) 
        req_msgs[i] = req_msgs[i][2:]
        
        if(len(req_msgs[i]) > BIT_WIDTH):
            req_msgs[i] = req_msgs[i][0:BIT_WIDTH]

        while(len(req_msgs[i]) < BIT_WIDTH):
            randnum = np.random.randint(0,2)
            req_msgs[i] += str(randnum)

    # print(req_msgs)
    return req_msgs

def XOR(a,b):
    if(int(a) == 0 and int(b) == 1):
        return 1
    elif(int(a) == 1 and int(b) == 0):
        return 1
    else:
        return 0

'''
def taps(Q, T1, T2, T3, T4):
    # Make Q backwards since Q is a string
    Q = Q[::-1]

    Q1 = Q[T1:T1+1]
    Q5 = Q[T2:T2+1]
    Q6 = Q[T3:T3+1]
    Q31 = Q[T4:T4+1]

    tap1 = XOR(int(Q6), int(Q31))
    tap2 = XOR(int(Q5), tap1)
    return XOR(int(Q1), tap2)
'''
def taps(Q, T1, T2, T3, T4):
    # Make Q backwards since Q is a string
    Q = Q[::-1]

    if(T3 != 0):
        Q1 = Q[T1:T1+1]
        Q5 = Q[T2:T2+1]
        Q6 = Q[T3:T3+1]
        Q31 = Q[T4:T4+1]

        tap1 = XOR(int(Q6), int(Q31))
        tap2 = XOR(int(Q5), int(Q1))
        ans = XOR(tap1, tap2)
        if(ans == 1): 
            return 0
        else:
            return 1
    else:
        Q1 = Q[T1:T1+1]
        Q5 = Q[T2:T2+1]

        return XOR(int(Q1), int(Q5))

# Functional Model ---------------------------------------------------------
def lfsr_model(SEED_ARRAY, NUM_MSGS, NUM_OUTPUTS, TAPS):
    # Initialize outgoing messages array
    resq_msgs = []
    
    # Loops for NUM_MSGS amount of times
    for i in range(NUM_MSGS):
        Q = SEED_ARRAY[i]
        resq_msgs.append([])

        # Calculate output of taps and append for NUM_OUTPUT loops
        for j in range(NUM_OUTPUTS):
            resq_msgs[i].append(Q)
            Q = Q[1:] + str(taps(Q,TAPS[0],TAPS[1],TAPS[2],TAPS[3]))

    # Initialize binary version of outgoing messages array
    final_resq_msgs = []

    # Convert strings -> binary values
    for i in range(NUM_MSGS):
        final_resq_msgs.append([])
        binarylist = convert_binary_strings_to_lists(resq_msgs[i])
        for array in binarylist:
            final_resq_msgs[i].append(binaryarray_to_binaryvalue(array))
    
    # Return binary values to compare with RTL
    return final_resq_msgs

# Tests ---------------------------------------------------------
# Checks that model outputs are equal to LFSR RTL outputs. 
# If resp_rdy is LOW, then the LFSR should stall and continue to output the same value.
async def lfsr_output_test(dut, NUM_SEEDS, SEED, MODEL_OUTPUTS, num_outputs):
    # Reset
    dut.reset.value = 1

    #Start clock
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    for i in range(NUM_SEEDS): 
        # Initialize: STATE = IDLE
        dut.reset.value = 1
        await ClockCycles(dut.clk, 1)
        await ClockCycles(dut.clk, 1)

        # IDLE -> GEN_VAL
        dut.reset.value = 0
        dut.req_val.value = 1

        # SEEDING LFSR
        print("Using seed: " + SEED[i])
        inputseed = [SEED[i]]
        inputseedlist = convert_binary_strings_to_lists(inputseed)
        inputbinary = binaryarray_to_binaryvalue(inputseedlist[0])
        print("HERE:")
        print(inputbinary)
        dut.req_msg.value = inputbinary
        dut.resp_rdy.value = 1
        await ClockCycles(dut.clk, 1)
        await ClockCycles(dut.clk, 1)
        
        # Checks that model outputs are equal to LFSR RTL outputs. 
        # If resp_rdy is LOW, then the LFSR should stall and continue to output the same value.
        j = 0
        while(j < num_outputs):
            assert dut.state.value == dut.GEN_VAL
            if(dut.resp_rdy.value == 1):
                assert dut.resp_msg.value == MODEL_OUTPUTS[i][j]
                j = j + 1
            else:
                assert dut.resp_msg.value == MODEL_OUTPUTS[i][j]
            dut.resp_rdy.value = not dut.resp_rdy.value
            await ClockCycles(dut.clk, 1)
        
# Tests FSM transitions. Singles out specific values to enter certain states.
async def lfsr_FSM_test(dut, BIT_WIDTH):
     # Reset
    dut.reset.value = 1

    #Start clock
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    # Initialize: STATE = IDLE
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    assert dut.next_state.value == dut.IDLE
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.IDLE
    assert(dut.resp_val.value == 0)
    assert(dut.req_rdy.value == 1)
    assert(dut.resp_msg.value == '0' * BIT_WIDTH)

    # IDLE -> GEN_VAL
    dut.reset.value = 0
    dut.req_val.value = 1
    dut.resp_rdy.value = 1
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.IDLE
    assert dut.next_state.value == dut.GEN_VAL
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.GEN_VAL
    assert(dut.req_rdy.value == 0)
    assert(dut.resp_val.value == 1)
    assert(not dut.resp_msg.value == '0' * BIT_WIDTH)
    
    # GEN_VAL -> GEN_VAL
    dut.reset.value = 0
    dut.req_val.value = 1
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.GEN_VAL
    assert dut.next_state.value == dut.GEN_VAL
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.GEN_VAL
    assert dut.state.value == dut.GEN_VAL
    assert(dut.req_rdy.value == 0)
    assert(dut.resp_val.value == 1)
    assert(not dut.resp_msg.value == '0' * BIT_WIDTH)

    # GEN_VAL -> IDLE
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.GEN_VAL
    assert dut.next_state.value == dut.IDLE
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.IDLE
    assert(dut.resp_val.value == 0)
    assert(dut.req_rdy.value == 1)
    assert(dut.resp_msg.value == '0' * BIT_WIDTH)

    '''
    # DEFAULT - UNCOMMENT TO CHECK DEFAULT CASE
    dut.reset.value = 1
    dut.req_val.value = 0
    await RisingEdge(dut.clk)
    dut.reset.value = 0
    await RisingEdge(dut.clk)
    assert dut.state.value == dut.IDLE
    
    dut.state.value = 0b11  
    await Timer(1, units="ns")
    assert dut.next_state.value == 0b00
    '''
    
# Manually checks LFSR outputs and internal states and logic.
async def lfsr_manual_test(dut):
     # Reset
    dut.reset.value = 1

    #Start clock
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)

    # Initialize: STATE = IDLE
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    assert dut.next_state.value == dut.IDLE


    print("Using seed: " + '11100111001011000100011100011011[i]')
    inputseed = ['11100111001011000100011100011011']
    inputseedlist = convert_binary_strings_to_lists(inputseed)
    inputbinary = binaryarray_to_binaryvalue(inputseedlist[0])
    dut.req_msg.value = inputbinary

    # IDLE -> GEN_VAL
    dut.reset.value = 0
    dut.req_val.value = 1
    dut.resp_rdy.value = 1
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.IDLE
    assert dut.next_state.value == dut.GEN_VAL
    await ClockCycles(dut.clk, 1)
    assert dut.state.value == dut.GEN_VAL
    assert dut.next_state.value == dut.GEN_VAL
    assert dut.resp_msg.value == inputbinary
    assert(dut.req_rdy.value == 0)
    assert(dut.resp_val.value == 1)

    # Cycle & Shift
    await ClockCycles(dut.clk, 1)
    inputseed = ['11001110010110001000111000110110']
    inputseedlist = convert_binary_strings_to_lists(inputseed)
    inputbinary = binaryarray_to_binaryvalue(inputseedlist[0])
    assert dut.resp_msg.value == inputbinary
    assert(dut.req_rdy.value == 0)
    assert(dut.resp_val.value == 1)
    assert dut.state.value == dut.GEN_VAL
    assert dut.next_state.value == dut.GEN_VAL

    # Cycle & Shift
    await ClockCycles(dut.clk, 1)
    inputseed = ['10011100101100010001110001101101']
    inputseedlist = convert_binary_strings_to_lists(inputseed)
    inputbinary = binaryarray_to_binaryvalue(inputseedlist[0])
    assert dut.resp_msg.value == inputbinary
    assert(dut.req_rdy.value == 0)
    assert(dut.resp_val.value == 1)
    assert dut.state.value == dut.GEN_VAL
    assert dut.next_state.value == dut.GEN_VAL


'''
This test checks the output of the LFSR for NUM_LFSR_OUTPUT cycles. 
Alter the number of seeds to seed the LFSR with NUM_SEEDS.
Parametrize the model with its BIT_WIDTH and an array of TAPS in the order of [T1, T2, T3, T4] as seen in the RTL.
'''
@cocotb.test()
async def LFSR_OUTPUT(dut):
    print("||| 1ST TEST: Q TEST |||")

    '''
    # Parameters
    NUM_SEEDS = 100
    LFSR_MSG_BITS = 32
    NUM_LFSR_OUTPUTS = 20
    TAPS = [1,5,6,31]
    '''

    # Parameters
    NUM_SEEDS = 1
    LFSR_MSG_BITS = 8
    NUM_LFSR_OUTPUTS = 5
    taps_dict = {
        2: [0, 1, 0, 0],
        3: [1, 2, 0, 0],
        4: [2, 3, 0, 0],
        5: [2, 4, 0, 0],
        6: [4, 5, 0, 0],
        7: [5, 6, 0, 0],
        8: [3, 4, 5, 7],
        9: [4, 8, 0, 0],
        10: [6, 9, 0, 0],
        11: [8, 10, 0, 0],
        12: [5, 7, 10, 11],
        13: [8, 9, 11, 12],
        14: [8, 10, 12, 13],
        15: [13, 14, 0, 0],
        16: [10, 12, 13, 15],
        17: [13, 16, 0, 0],
        18: [10, 17, 0, 0],
        19: [13, 16, 17, 18],
        20: [16, 19, 0, 0],
        21: [18, 20, 0, 0],
        22: [20, 21, 0, 0],
        23: [17, 22, 0, 0],
        24: [19, 20, 22, 23],
        25: [21, 24, 0, 0],
        26: [19, 23, 24, 25],
        27: [21, 24, 25, 26],
        28: [24, 27, 0, 0],
        29: [26, 28, 0, 0],
        30: [23, 25, 28, 29],
        31: [27, 30, 0, 0],
        32: [25, 26, 29, 31],
        33: [19, 32, 0, 0],
        34: [25, 29, 30, 33],
        35: [32, 34, 0, 0],
        36: [24, 35, 0, 0],
        37: [30, 32, 35, 36],
        38: [31, 32, 36, 37],
        39: [34, 38, 0, 0],
        40: [34, 35, 36, 39],
        41: [37, 40, 0, 0],
        42: [34, 36, 39, 41],
        43: [36, 37, 41, 42],
        44: [37, 38, 41, 43],
        45: [40, 41, 43, 44],
        46: [37, 38, 39, 45],
        47: [41, 46, 0, 0],
        48: [38, 40, 43, 47],
        49: [39, 48, 0, 0],
        50: [45, 46, 47, 49],
        51: [44, 47, 49, 50],
        52: [48, 51, 0, 0],
        53: [46, 50, 51, 52],
        54: [45, 47, 50, 53],
        55: [30, 54, 0, 0],
        56: [48, 51, 53, 55],
        57: [49, 56, 0, 0],
        58: [38, 57, 0, 0],
        59: [51, 54, 56, 58],
        60: [58, 59, 0, 0],
        61: [55, 58, 59, 60],
        62: [55, 56, 58, 61],
        63: [61, 62, 0, 0],
        64: [59, 60, 62, 63],
        65: [46, 64, 0, 0],
        66: [56, 57, 59, 65],
        67: [61, 64, 65, 66]
    }
    TAPS = taps_dict[LFSR_MSG_BITS]

    # Generating seeds and subsequent model outputs
    SEEDS = generate_seeds(NUM_SEEDS, LFSR_MSG_BITS)
    MODEL_OUTPUTS = lfsr_model(SEEDS, NUM_SEEDS, NUM_LFSR_OUTPUTS, TAPS)

    '''
    # Generating seeds and subsequent model outputs
    SEEDS = generate_seeds(NUM_SEEDS, LFSR_MSG_BITS)
    MODEL_OUTPUTS = lfsr_model(SEEDS, NUM_SEEDS, NUM_LFSR_OUTPUTS, TAPS)
    '''
    
    # Test
    await lfsr_output_test(dut, NUM_SEEDS, SEEDS, MODEL_OUTPUTS, NUM_LFSR_OUTPUTS)

'''
This test checks the FSM transitions and ensures that internal logic remains correct through transitions.
'''
@cocotb.test()
async def LFSR_FSM(dut):
    print("||| 2ND TEST: FSM TEST |||")

    # Parameters
    LFSR_MSG_BITS = 32

    # Test
    await lfsr_FSM_test(dut, LFSR_MSG_BITS)

'''
This test manually checks LFSR outputs and internal states and logic.
'''
@cocotb.test()
async def LFSR_MANUAL(dut):
    print("||| 3RD TEST: MANUAL TEST |||")

    # Test
    await lfsr_manual_test(dut)

