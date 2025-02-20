import sys
import os
import pdb

# Add MISR and LFSR models to path
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'misr','tests'))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'lfsr','tests'))
from misr_model import *
from lfsr_model import *


# Performs multiplication on a 32 bit binary number.
# binary_str_in --> 32 binary number (str)
def multiply_binary(binary_str_in):
    binary_str=str(binary_str_in)
    a = binary_str[:16]
    b = binary_str[16:]

    # print("a: "+a)
    # print("b: "+b)
    # print(f"a: {int(a, 2)}")
    # print(f"b: {int(b,2)}")
    
    
    assert len(a)==len(b),"size of a not the same as b..."
    a = int(binary_str[:16],2)
    b = int(binary_str[16:],2)

    result = a * b

    # Preserve only the LSB 16 bits
    lsb_16_bits = result & 0xFFFF

    # Convert to binary and remove the '0b' prefix
    binary_str = bin(lsb_16_bits)[2:]

    # Zero-pad to ensure it's 16 bits long
    binary_str = binary_str.zfill(16)

    # print(f"LSB 16 bits (binary): {binary_str}")
    result_as_int = int(binary_str, 2)
    
    return result_as_int


# generates a set of seeds given an array of LFSR test vectors
def gen_signatures(inputs):
    # Dictionary to store the seeds
    outputs = {}
    for array in inputs:

        # Seed for each input array
        seed = None

        # Entry in each input array
        entry_idx = 0

        # Iterate over all entries in input array
        str_array = list(map(lambda x: str(x), array))
        for entry in str_array:

            # Capture the seed
            if (entry_idx == 0):
                seed = entry

            # Get the product
            product = multiply_binary(entry)

            # If the seed is not in the outputs dict, add it 
            if seed not in outputs:
                outputs[seed] = [product]
            else:
                outputs[seed].append(product)
            
            # increment idx
            entry_idx += 1
        
        # Calculate the signature
        signature = misr_model(outputs[seed],[0]*16)
        outputs[seed] = signature
    
    return outputs
    
# Generates lists of test vectors given a list of seeds. 
def gen_lfsr_vectors(seeds, num_vectors):
    outputs = []
    for seed in seeds:
        vectors = lfsr_model([seed], 1, num_vectors)
        outputs.append(vectors[0])
    return outputs


# ADD SEEDS HERE
seeds = [
    '01010101000111000101101111111011',
    '10000111001110100111100001011100',
    '11101101011001111010101100101101',
    '00110011001100110011001100110011',
    '10101010101010101010101010101010',
    '11001100110011001100110011001100',
    '10101010101010111111111000110101',
    '10000000000011110101111010101011',
    '00000000000000000000000000000000',
    '11111111111111111111111111111111',
    '11111111111111100000000000000000',
    '01101101100011101010111010101111'
]

test_vectors = gen_lfsr_vectors(seeds, 20)
signatures = gen_signatures(test_vectors)
for key in signatures:
    print(f"{key}: {signatures[key]}")

# pdb.set_trace()