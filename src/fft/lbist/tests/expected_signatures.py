import sys
import os

# Add MISR and LFSR models to path
sys.path.append("/home/ars437/c2s2/c2s2_ip")
sys.path.append("/classes/c2s2/easybuild/software/Python/3.11.5-GCCcore-13.2.0/lib64/python3.11/site-packages")
from src.fft.pease.sim import fft
from src.lbist.misr.tests.misr_model import misr_model
from src.lbist.lfsr.tests.lfsr_functional_galois import lfsr_model, taps_dict
from fixedpt import CFixed

def fft_model(binary_strs_in):
    # Converts 64 bit input string to 4 16 bit binary values
    inputs = [int(binary_strs_in[i], 2) for i in range(4)]
    
    # Converts each input to a complex number
    inputs = [CFixed((x, 0), 32, 0) for x in inputs]
    
    results = fft(inputs, 32, 0, 4)
    
    # Convert output complex numbers to integers
    results = [x.real.get(True) & 0xffff for x in results]
    
    return results


# generates a set of seeds given an array of LFSR test vectors
def gen_signatures(inputs: list, inputs_per_seed: int):
    # Dictionary to store the seeds
    outputs = {}
    for array in inputs:

        # Seed for each input array
        seed = None

        # Iterate over all entries in input array
        str_array = list(map(lambda x: str(x), array))
        for entry_index in range(0, len(str_array), inputs_per_seed):
            # Capture the seed
            if (entry_index == 0):
                seed = str_array[entry_index]

            # Get the fft output
            fft_output = fft_model(str_array[entry_index: entry_index + inputs_per_seed])

            # If the seed is not in the outputs dict, add it 
            if seed not in outputs:
                outputs[seed] = fft_output
            else:
                outputs[seed] += fft_output
        
        # Calculate the signature
        signature = misr_model(outputs[seed],[0]*16)
        outputs[seed] = signature
    
    return outputs
    
# Generates lists of test vectors given a list of seeds. 
def gen_lfsr_vectors(seeds, num_vectors):
    vectors = lfsr_model(seeds, len(seeds), num_vectors, taps_dict[32])
    return vectors


# ADD SEEDS HERE
seeds = [
    '10101110100101100000101111000010',
    '10000111001110100111100001011100',
    '10001111101000100111111010010111',
    '10111010000110110000000000110111'
]

test_vectors = gen_lfsr_vectors(seeds, 80)

signatures = gen_signatures(test_vectors, 4)
for key in signatures:
    print(f"{key}: {signatures[key]}")
    # print(f"{hex(int(key, 2))}: {hex(int(signatures[key].binstr, 2))}")