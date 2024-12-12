from cocotb.binary import BinaryValue
import random

# Global Params ------------------------------------------------------------
TB_SEED = "DEADBEEF"
NUM_TESTS = 1000

# Functional Model ---------------------------------------------------------
def misr_model(int_array, seed):
    signature = seed
    for num in int_array:
        # Convert integer to binary with the same length as the seed, then to a list of bits
        binary_entry = [int(bit) for bit in bin(num)[2:].zfill(len(seed))]

        # Do the xor
        for i in range(len(signature)):
            signature[i] = signature[i] ^ binary_entry[i]

        # Do the bitshift
        signature_msb = signature[0]
        for i in range(1, len(signature)):
            signature[i - 1] = signature[i]

        # Place the original MSB at the end
        signature[-1] = signature_msb
        # print(signature)

    return binaryarray_to_binaryvalue(signature)

# Helper tasks -------------------------------------------------------------
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



# # Generates an array of random positive integers with a maximum value of 4294967294.
# # - size (int): The number of random integers to generate.
# # - number of bits of each input
# def generate_random_array(size, num_bits):
#     random.seed(TB_SEED)
#     max_value = 2**num_bits -1
#     return [random.randint(1, max_value) for _ in range(size)]
