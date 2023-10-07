# Tools file to parametrize multipliers
from random import randint
import pytest


# Create test parametrization information
# execution_number: number of times to run the test
# sequence_lengths: numbers of inputs to stream through the block
# n: bounds on number of bits in the fixed point number
# d: bounds on number of decimal bits in the fixed point number
def mk_params(execution_number, sequence_lengths, n, d, slow=False):
    if isinstance(n, int):
        n = (n, n)
    if isinstance(d, int):
        d = (d, d)

    res = []

    for j in range(execution_number):
        for i in sequence_lengths:
            rn = randint(n[0], n[1])
            rd = randint(d[0], min(rn - 1, d[1]))
            res.append(
                pytest.param(
                    j,  # execution_number index (unused)
                    i,  # number of inputs to stream
                    rn,  # randomly generated `n`
                    rd,  # randomly generated `d`
                    id=f"{i} {rn}-bit, {rd}-decimal-bit numbers",
                    marks=pytest.mark.slow if slow else [],
                )
            )
    return res
