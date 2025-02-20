import sys
import os

# Add MISR and LFSR models to path
sys.path.append("/home/ars437/c2s2/c2s2_ip")
sys.path.append("/classes/c2s2/easybuild/software/Python/3.11.5-GCCcore-13.2.0/lib64/python3.11/site-packages")
from src.fft.pease.sim import fft
from src.lbist.misr.tests.misr_model import misr_model
from src.lbist.lfsr.tests.lfsr_functional_galois import lfsr_model, taps_dict
from fixedpt import CFixed

def fft_model(binary_str_in):
    binary_str=str(binary_str_in)
    
    # Converts 64 bit input string to 4 16 bit binary values
    inputs = [int(binary_str[16*x : 16*(x+1)], 2) for x in range(4)]
    
    # Converts each input to a complex number
    inputs = [CFixed((x, 0), 16, 8) for x in inputs]

    results = fft(inputs, 16, 8, 4)
    
    # Convert output complex numbers to integers
    results = [x.real.get(True) for x in results]

    # Convert to binary and remove the '0b' prefix
    binary_strs = [str(bin(x))[2:] for x in results]

    # Zero-pad to ensure it's 16 bits long
    binary_strs = (x.zfill(16) for x in binary_strs)
    
    # Concatenate output strings
    result_str = ''.join(binary_strs)

    # print(f"LSB 16 bits (binary): {binary_str}")
    result_as_int = int(result_str, 2)
    
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

            # Get the fft output
            fft_output = fft_model(entry)

            # If the seed is not in the outputs dict, add it 
            if seed not in outputs:
                outputs[seed] = [fft_output]
            else:
                outputs[seed].append(fft_output)
            
            # increment idx
            entry_idx += 1
        
        # Calculate the signature
        signature = misr_model(outputs[seed],[0]*64)
        outputs[seed] = signature
    
    return outputs
    
# Generates lists of test vectors given a list of seeds. 
def gen_lfsr_vectors(seeds, num_vectors):
    vectors = lfsr_model(seeds, len(seeds), num_vectors, taps_dict[64])
    return vectors


# ADD SEEDS HERE
seeds = [
    '1010111010010110000010111100001010101110011111000100111000000111',
    '1000011100111010011110000101110010111011001011100011100011110110',
    '1000111110100010011111101001011101110101000010011111110011110000',
    '1011101000011011000000000011011111010000101000110101000101011110'
]

test_vectors = gen_lfsr_vectors(seeds, 20)
signatures = gen_signatures(test_vectors)
for key in signatures:
    print(f"{key}: {signatures[key]}")