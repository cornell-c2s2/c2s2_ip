import pytest
import random
import struct
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib.test_utils import mk_test_case_table
from pymtl3.stdlib import stream
from src.floating_point.harnesses.comb_float_multiplier import CombFloatMultiplier


# Creates a test harness class for the `CombFloatMultiplier` module.
class Harness(Component):
    def construct(s, harness):
        s.harness = harness

        s.src0 = stream.SourceRTL(mk_bits(32))
        s.src1 = stream.SourceRTL(mk_bits(32))
        s.sink = stream.SinkRTL(mk_bits(32))

        # connect the harness to the python wrapper
        s.src0.send //= s.harness.in0
        s.src1.send //= s.harness.in1
        s.harness.out //= s.sink.recv

    def done(s):
        return s.src0.done() and s.src1.done() and s.sink.done()


# Initialize a simulatable model
def create_model():
    model = CombFloatMultiplier()

    # Create a harness wrapping our `CombFloatMultiplier` module.
    return Harness(model)


def f32_as_int(x):
    bytes = struct.pack(">f", x)
    return int.from_bytes(bytes, byteorder="big")


def int_as_f32(x):
    bytes = x.to_bytes(length=4, byteorder="big")
    return struct.unpack(">f", bytes)[0]

# def basic_test():
    

# test_case_table = mk_test_case_table([

#     (        "in0             in1             out"),
#     ["basic", int_as_f32(1),  int_as_f32(1),  int_as_f32(1) ]
# ])


# @pytest.mark.parametrize( **test_case_table )
def test_simple():
    # Create our model.
    model = create_model()

    # model.set_param(
    #     "top.src0.contruct",
    #     msgs=[int_as_f32(1)],
    #     initial_delay=0,
    #     interval_delay=0,
    # )

    # model.set_param(
    #     "top.src1.construct",
    #     # Input values to stream through the block in order
    #     msgs=[int_as_f32(1)],
    #     # Cycles to wait after reset before starting to send inputs
    #     initial_delay=0,
    #     # Cycles to wait before sending next input (before `send_val` set high)
    #     interval_delay=0,
    # )

    # model.set_param(
    #     "top.sink.construct",
    #     # Expected output values to read from the block in order
    #     msgs=[int_as_f32(1)],
    #     # Cycles to wait after reset before setting `recv_rdy` to high
    #     initial_delay=0,
    #     # Cycles to wait between outputs before setting `recv_rdy` to high
    #     interval_delay=0,
    # )

    # run_sim(
    #     model,
    #     cmdline_opts={
    #         "dump_textwave": False,
    #         # Creates the vcd file test_simple_<bitwidth>.vcd for debugging.
    #         "dump_vcd": f"basic test",
    #         # Optional, used to test accurate cycle counts.
    #         "max_cycles": None,
    #     },
    # )

    run_test_vector_sim(
        CombFloatMultiplier(),
        [("in0 in1 out"),[int_as_f32(1),  int_as_f32(1),  int_as_f32(1)]],
        cmdline_opts={},
    )
    

