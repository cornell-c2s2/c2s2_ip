# Imports needed by cocotb
from pathlib import Path
import numpy as np
from cocotb.binary import BinaryValue

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

    print(req_msgs)
    return req_msgs

def XOR(a,b):
    if(int(a) == 0 and int(b) == 1):
        return 1
    elif(int(a) == 1 and int(b) == 0):
        return 1
    else:
        return 0

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

# Parameters
NUM_SEEDS = 1
LFSR_MSG_BITS = 8
NUM_LFSR_OUTPUTS = 5
taps_dict = {
    2 : [0,1,0,0],
    3 : [0,2,0,0],
    4 : [0,3,0,0],
    5 : [1,4,0,0],
    6 : [0,5,0,0],
    7 : [0,6,0,0],
    8 : [1,2,3,7],
    9 : [3,8,0,0],
    10 : [2,9,0,0],
    11 : [1,10,0,0],
    12 : [0,3,5,11],
    13 : [0,2,3,12],
    14 : [0,2,4,13],
    15 : [0,14,0,0],
    16 : [1,2,4,15],
    17 : [2,16,0,0],
    18 : [6,17,0,0],
    19 : [0,1,4,18],
    20 : [2,19,0,0],
    21 : [1,20,0,0],
    22 : [0,21,0,0],
    23 : [4,22,0,0],
    24 : [0,2,3,23],
    25 : [2,24,0,0],
    26 : [0,1,5,25],
    27 : [0,1,4,26],
    28 : [2,27,0,0],
    29 : [1,28,0,0],
    30 : [0,3,5,29],
    31 : [2,30,0,0],
    32 : [1,5,6,31],
    64 : [60, 61, 63, 64]
}
TAPS = taps_dict[LFSR_MSG_BITS]

# Generating seeds and subsequent model outputs
SEEDS = generate_seeds(NUM_SEEDS, LFSR_MSG_BITS)
output = lfsr_model(SEEDS, NUM_SEEDS, NUM_LFSR_OUTPUTS, TAPS)
print(output)