import pytest
import random
import struct
import os
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib.test_utils import mk_test_case_table
from pymtl3.stdlib import stream
from src.floating_point.comb.harnesses.multiplier import CombFloatMultiplierWrapper


# Creates a test harness class for the `CombFloatMultiplier` module.
class Harness(Component):
    def construct(s, harness):
        s.harness = harness

        s.src0 = stream.SourceRTL(mk_bits(32))
        s.src1 = stream.SourceRTL(mk_bits(32))
        s.sink = stream.SinkRTL(mk_bits(32))

        # bind the harness to the dut (that is within the wrapper)!
        s.src0.send //= s.harness.in0
        s.src1.send //= s.harness.in1
        s.harness.out //= s.sink.recv

    def done(s):
        return s.src0.done() and s.src1.done() and s.sink.done()


# Initialize a simulatable model
def create_model():
    model = CombFloatMultiplierWrapper()

    # Create a harness wrapping our `CombFloatMultiplier` module.
    return Harness(model)


def f32_as_int(x):
    bytes = struct.pack(">f", x)
    return int.from_bytes(bytes, byteorder="big")


def int_as_f32(x):
    bytes = x.to_bytes(length=4, byteorder="big")
    return struct.unpack(">f", bytes)[0]


def test_simple():
    # Create our model.
    model = create_model()

    run_test_vector_sim(
        CombFloatMultiplierWrapper(32, 23, 8),  # dut
        [("in0 in1 out"), [int_as_f32(3), int_as_f32(2), int_as_f32(6)]],  # test cases
        cmdline_opts={},
    )


# note: this test requires that the test cases have already been piped to the test_fifo
# using the testfloat_gen() function
# http://www.jhauser.us/arithmetic/TestFloat-3/doc/testfloat_gen.html
@pytest.mark.slow
def test_with_berkeley_library(testfloat_gen):
    # Create our model.
    model = create_model()

    testfloat_data = testfloat_gen("f32_mul", level=1)

    # Truncate the error flags here because we don't want them.
    testfloat_data = [test_case[0:3] for test_case in testfloat_data]

    run_test_vector_sim(
        CombFloatMultiplierWrapper(32, 23, 8),  # dut
        [("in0 in1 out"), *testfloat_data],  # test cases
        cmdline_opts={},
    )
