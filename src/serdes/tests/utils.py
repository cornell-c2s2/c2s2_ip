import random
from pymtl3 import mk_bits


# Return a random serdes spec
def rand_spec(max_bus=1024):
    n_samples = random.randint(1, max_bus - 1)
    # n_bits is capped here because pymtl3 does not support bit widths greater than or equal to 1024
    n_bits = random.randint(1, (max_bus - 1) // n_samples)
    return (n_samples, n_bits)


# Creates a list of `nmsgs` random transactions
# for a serdes with `nbits` bits and `nsamples` samples
def create_transactions(nbits, nsamples, nmsgs):
    bits = mk_bits(nbits)
    return [
        [bits(random.randint(0, (1 << nbits) - 1)) for __ in range(nsamples)]
        for _ in range(nmsgs)
    ]
