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
            res.append(
                pytest.param(
                    j,  # execution_number index (unused)
                    i,  # number of inputs to stream
                    n,  # bounds for `n`
                    d,  # bounds for `d`
                    id=f"{i} ({n[0]}-{n[1]})-bit, ({d[0]}-{d[1]})-decimal-bit numbers",
                    marks=pytest.mark.slow if slow else [],
                )
            )
    return res


# Random fixed point number specification
def rand_fxp_spec(n, d):
    rn = randint(n[0], n[1])
    rd = randint(d[0], min(rn - 1, d[1]))
    return (rn, rd)
