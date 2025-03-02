import sys
import os

# Import functional models
sys.path.append("../../../../")
sys.path.append("/classes/c2s2/easybuild/software/Python/3.11.5-GCCcore-13.2.0/lib64/python3.11/site-packages")
from src.fft.pease.sim import fft
from src.lbist.misr.tests.misr_model import misr_model
from src.lbist.lfsr.tests.lfsr_functional_galois import lfsr_model, taps_dict
from fixedpt import CFixed

SEED_BITS = 32
FFT_ARRAY_LENGTH = 4
DECIMAL_BIT = 4

# Must be divisible by FFT_ARRAY_LENGTH
TOTAL_FFT_INPUTS = 80

def fft_model(binary_strs_in):
    # Converts 64 bit input string to 4 16 bit binary values
    inputs = [int(binary_strs_in[i], 2) for i in range(FFT_ARRAY_LENGTH)]
    
    # Converts each input to a complex number
    inputs = [CFixed((x, 0), SEED_BITS, DECIMAL_BIT, True) for x in inputs]

    # Get fft output
    results = fft(inputs, SEED_BITS, DECIMAL_BIT, FFT_ARRAY_LENGTH)
    
    # Convert output complex numbers to real integers, only use half bits
    results = [x.real.get(True) & ((1 << (SEED_BITS // 2)) - 1) for x in results]
        
    return results


# generates a set of seeds given an array of LFSR test vectors
def gen_signatures(inputs: list):
    # Dictionary to store the seeds
    outputs = {}
    for array in inputs:

        # Seed for each input array
        seed = None

        # Iterate over all entries in input array
        str_array = [str(x) for x in array] 
        for entry_index in range(0, len(str_array), FFT_ARRAY_LENGTH):
            # Capture the seed
            if (entry_index == 0):
                seed = str_array[entry_index]

            # Get the fft output
            fft_output = fft_model(str_array[entry_index: entry_index + FFT_ARRAY_LENGTH])

            # If the seed is not in the outputs dict, add it 
            if seed not in outputs:
                outputs[seed] = fft_output
            else:
                outputs[seed] += fft_output
        
        # Calculate the signature
        signature = misr_model(outputs[seed],[0]*(SEED_BITS // 2))
        outputs[seed] = signature
    
    return outputs
    
# Generates lists of test vectors given a list of seeds. 
def gen_lfsr_vectors(seeds, num_vectors):
    vectors = lfsr_model(seeds, len(seeds), num_vectors, taps_dict[SEED_BITS])
    return vectors


# ADD SEEDS HERE
seeds = [
    '10101110100101100000101111000010',
    '10000111001110100111100001011100',
    '10001111101000100111111010010111',
    '10111010000110110000000000110111'
]

test_vectors = gen_lfsr_vectors(seeds, TOTAL_FFT_INPUTS)
signatures = gen_signatures(test_vectors)
for key in signatures:
    print(f"{key}: {signatures[key]}")
    # print(f"{hex(int(key, 2))}: {hex(int(signatures[key].binstr, 2))}")