"""
A useful library of PYMTL3 test helper functions
"""

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
