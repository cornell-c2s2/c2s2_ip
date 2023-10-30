import pytest
import struct
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib import stream
from src.floating_point.comb.harnesses.multiplier import CombFloatMultiplierWrapper


# Converts a (python) float to its bits representation as an integer
def f32_as_int(x):
    bytes = struct.pack(">f", x)
    return int.from_bytes(bytes, byteorder="big")


# Converts a (python) integer representing a float directly into a float
def int_as_f32(x):
    bytes = x.to_bytes(length=4, byteorder="big")
    return struct.unpack(">f", bytes)[0]


def test_simple(cmdline_opts):
    run_test_vector_sim(
        CombFloatMultiplierWrapper(32, 23, 8),  # dut
        [
            ("in0 in1 out*"),
            [f32_as_int(0), f32_as_int(0), f32_as_int(0)],
            [f32_as_int(1), f32_as_int(1), f32_as_int(1)],
            [f32_as_int(3), f32_as_int(2), f32_as_int(6)],
        ],  # test cases
        cmdline_opts,
    )


# note: this test requires that the test cases have already been piped to the test_fifo
# using the testfloat_gen() function
# http://www.jhauser.us/arithmetic/TestFloat-3/doc/testfloat_gen.html
@pytest.mark.slow
def test_with_testfloat(testfloat_gen, cmdline_opts):
    # Generate 100,000 test cases from testfloat.
    testfloat_data = testfloat_gen("f32_mul", level=1, n=100_000)

    # Truncate the error flags here because we don't want them.
    testfloat_data = [test_case[0:3] for test_case in testfloat_data]

    run_test_vector_sim(
        CombFloatMultiplierWrapper(32, 23, 8),  # dut
        [("in0 in1 out*"), *testfloat_data],  # test cases
        cmdline_opts,
    )
