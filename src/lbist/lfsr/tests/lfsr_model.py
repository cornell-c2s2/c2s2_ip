import random
from cocotb.binary import BinaryValue
import pdb


# Helper Functions ---------------------------------------------------------------------------------
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


# Coverts binary array to cocotb.binary,BinaryValue
# Ex: [0, 1, 0, 1] ==> 0101
def binaryarray_to_binaryvalue(binary_list):
    binary_string = ''.join(str(bit) for bit in binary_list)
    return BinaryValue(binary_string)


# Converts ['101', '001', '111'] to  [[1, 0, 1], [0, 0, 1], [1, 1, 1]]
def convert_binary_strings_to_lists(binary_strings):
    return [[int(bit) for bit in binary_string] for binary_string in binary_strings]


# Functional Model----------------------------------------------------------------------------------
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

# TODO ADD description here
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



x=lfsr_model(["11100010110011011001110101000111"], 1, 5)
# pdb.set_trace()