"""
A useful library of PYMTL3 test helper functions
"""

from collections import namedtuple
import pytest
from pymtl3 import mk_bits, concat, bitstruct, Bits
from pymtl3.stdlib.test_utils import mk_test_case_table as mk_test_case_table_native
from fixedpt import Fixed, CFixed


# -----------------------------------------------------------------------
# Comparison Functions
# -----------------------------------------------------------------------


# Exact comparison
def cmp_exact(x: Bits, y: Bits):
    return x == y


# Approximate comparison
def cmp_approx(x: Bits, y: Bits, n: float):
    """
    In this comparison function, we want to ensure that the FFT
    is accurate within a fraction n.

    In other words, this checks whether n * max(|x|, |y|) > |x - y|
    If n = 0.01, then we are checking whether the difference is within 1%
    of the largest magnitude.

    Args:
        x (Bits): First number
        y (Bits): Second number
        n (float): Accuracy requirement
    """

    x = x.int()
    y = y.int()

    diff = abs(x - y)

    # Get the largest magnitude
    max_val = max(abs(x), abs(y))

    # If the difference is less than or equal to n times of the largest magnitude
    # Then we consider the values to be the same
    return diff <= max_val * n


# Create a comparison function with a specific lenience
def mk_cmp_approx(n: float):
    return lambda x, y: cmp_approx(x, y, n)


# Creates a transaction packer from a list of transaction sizes
# Takes arguments in the form of either:
#   - n arguments, each referring to the size of the corresponding transaction field
#   - a single value, which is the size of all transaction fields
# Returns:
#   - a function that takes n arguments, each referring to the value of the corresponding transaction field to pack.
#       - This function returns the packed transaction as one Bits object
def mk_packed(*args):
    def packer(*vals):
        nonlocal args
        # If we only have one argument, we assume it is the size of all transaction fields
        if len(args) == 1:
            args = args * len(vals)

        # Make sure we have matching numbers of arguments and values
        assert len(vals) == len(args)
        return concat(*[mk_bits(args[i])(vals[i]) for i in range(len(args))])

    return packer


# Creates a bitstruct with one field representing its list.
def mk_list_bitstruct(nbits, nsamples):
    @bitstruct
    class ListStruct:
        list: [mk_bits(nbits) for _ in range(nsamples)]

    return ListStruct


# Helper function that does the same thing as `mk_test_case_table` but allows for marking tests slow
# Treats a column in `mk_test_case_table` named `slow` as a boolean flag to mark the test as slow
def mk_test_case_table(test_cases):
    print(test_cases)
    table = mk_test_case_table_native(test_cases)

    params = {
        "argnames": table["argnames"],
        "argvalues": [],
    }

    for i in range(len(table["ids"])):
        vals = table["argvalues"][i]
        try:
            slow = getattr(vals, "slow")
        except AttributeError:
            slow = False

        params["argvalues"].append(
            pytest.param(
                vals,
                id=table["ids"][i],
                # Adds the slow mark if the test case has the `slow` flag set to True
                marks=pytest.mark.slow if slow else [],
            )
        )

    return params


# Creates a matrix of transactions
# Takes a dictionary of transaction fields and their value ranges
# and returns a set of tests with all possible combinations of values
# USAGE:
# @pytest.mark.parametrize(*mk_test_matrix({
#  "field1": [1, 2, 3],
# "field2": [4, 5, 6],
# }, slow=False))
# def test_something(p):
#   print(p.field1) # ranges from 1 to 3
#   print(p.field2) # ranges from 4 to 6
#
def mk_test_matrix(values, slow=False):
    keys = []
    params = [[]]
    for k, v in values.items():
        if not isinstance(v, list):
            v = [v]
        keys.append(k)
        params = [[*p, (k, t)] for t in v for p in params]

    tp = namedtuple("_".join(keys), keys)

    def smartstr(v):
        if "__name__" in dir(v):
            return v.__name__
        # If this is a callable, get the name of the function
        if callable(v):
            return v.__name__
        if isinstance(v, list):
            return f"[{','.join([smartstr(x) for x in v])}]"
        if isinstance(v, tuple):
            return f"({','.join([smartstr(x) for x in v])})"
        return str(v)

    params = [
        pytest.param(
            tp(**dict(p)),
            id=",".join([f"{p[i][0]}={smartstr(p[i][1])}" for i in range(len(keys))]),
            marks=pytest.mark.slow if slow else [],
        )
        for p in params
    ]
    return ["p", params]


# Can make multiple test matrices.
# Takes any number of dictionaries of transaction fields and their value ranges
# USAGE:
# @pytest.mark.parametrize(*mk_test_matrices({
#   "field1": [1, 2, 3],
#   "field2": [4, 5, 6],
#   "slow": True
# }, {
#   "field1": [1, 2, 3],
#   "field2": [4, 5, 6],
#   "slow": False
# }))
# def test_something(p):
#   print(p.field1) # ranges from 1 to 3
#   print(p.field2) # ranges from 4 to 6
#
def mk_test_matrices(*args):
    return [
        "p",
        sum([(mk_test_matrix(arg, arg.get("slow", False))[1]) for arg in args], []),
    ]


# Cast a Fixed object to a Bits object
def fixed_bits(f: Fixed) -> Bits:
    value = f.get()

    return mk_bits(len(f))(value)


# Cast a CFixed object to a tuple of Bits objects
def cfixed_bits(cf: CFixed) -> tuple[Bits, Bits]:
    return fixed_bits(cf.real), fixed_bits(cf.imag)


# Convert a Bits object to an unsigned integer
def uint(x: Bits) -> int:
    i = int(x)
    if i < 0:
        i += 1 << len(x)
    return i
