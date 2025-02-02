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
    2: [1, 2],
    3: [2, 3],
    4: [3, 4],
    5: [3, 5],
    6: [5, 6],
    7: [6, 7],
    8: [5, 6, 8],
    9: [5, 9],
    10: [7, 10],
    11: [9, 11],
    12: [8, 11, 12],
    13: [9, 10, 12, 13],
    14: [9, 11, 13, 14],
    15: [11, 13, 14, 15],
    16: [11, 14, 16],
    17: [14, 15, 16, 17],
    18: [11, 13, 16, 17, 18],
    19: [14, 17, 18, 19],
    20: [16, 17, 19, 20],
    21: [19, 20, 21],
    22: [18, 17, 19, 22],
    23: [18, 20, 22, 23],
    24: [20, 21, 22, 23, 24],
    25: [22, 25],
    26: [20, 24, 25, 26],
    27: [22, 25, 26, 27],
    28: [24, 25, 26, 28],
    29: [24, 26, 27, 29],
    30: [24, 26, 29, 30],
    31: [28, 29, 30, 31],
    32: [25, 26, 29, 30, 32],
    33: [20, 27, 29, 32, 33],
    34: [26, 30, 31, 34],
    35: [27, 28, 34, 35],
    36: [25, 28, 29, 35, 36],
    37: [31, 33, 36, 37],
    38: [32, 33, 37, 38],
    39: [32, 35, 38, 39],
    40: [35, 36, 37, 40],
    41: [38, 39, 40, 41],
    42: [35, 37, 40, 42],
    43: [37, 38, 42, 43],
    44: [38, 39, 42, 44],
    45: [41, 42, 44, 45],
    46: [38, 39, 40, 46],
    47: [42, 47],
    48: [41, 39, 44, 48],
    49: [40, 43, 45, 49],
    50: [46, 47, 48, 50],
    51: [48, 45, 50, 51],
    52: [49, 46, 51, 52],
    53: [47, 51, 52, 53],
    54: [46, 48, 51, 54],
    55: [49, 53, 54, 55],
    56: [49, 52, 54, 56],
    57: [50, 52, 54, 57],
    58: [52, 53, 57, 58],
    59: [52, 55, 57, 59],
    60: [56, 55, 58, 60],
    61: [56, 59, 60, 61],
    62: [56, 57, 59, 62],
    63: [58, 59, 62, 63],
    64: [60, 61, 63, 64],
    65: [47, 61, 62, 65],
    66: [60, 57, 66],
    67: [62, 65, 66, 67]

}
TAPS = taps_dict[LFSR_MSG_BITS]

# Generating seeds and subsequent model outputs
SEEDS = generate_seeds(NUM_SEEDS, LFSR_MSG_BITS)
output = lfsr_model(SEEDS, NUM_SEEDS, NUM_LFSR_OUTPUTS, TAPS)
print(output)