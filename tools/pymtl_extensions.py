"""
A useful library of PYMTL3 test helper functions
"""

from collections import namedtuple
import pytest
from pymtl3 import mk_bits, concat
from pymtl3.stdlib.test_utils import mk_test_case_table as mk_test_case_table_native


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

    params = [
        pytest.param(
            tp(**dict(p)),
            id=",".join([f"{p[i][0]}={p[i][1]}" for i in range(len(keys))]),
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
