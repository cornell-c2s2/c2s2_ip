import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib.test_utils import mk_test_case_table
from pymtl3.stdlib import stream
from src.floating_point.harnesses.comb_float_adder import CombFloatAdder


# Creates a test harness class for the `CombFloatMultiplier` module.
class TestHarness(Component):
    def construct(s, comb_float_adder, BIT_WIDTH=32):
        s.src0 = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.src1 = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.comb_float_adder = comb_float_adder

        # connect the harness to the python wrapper
        s.src0.send //= s.comb_float_adder.a
        s.src1.send //= s.comb_float_adder.b
        s.comb_float_adder.out //= s.sink.result

    def done(s):
        return s.src0.done() and s.src1.done() and s.sink.done()


def basic():
    return [0b01000000000000000000000000000000]


test_case_table = mk_test_case_table(
    [
        ("msgs a b"),
        [
            "basic",
            basic,
            0b00111111100000000000000000000000,
            0b00111111100000000000000000000000,
        ],
    ]
)


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    # Create our model.
    model = TestHarness(CombFloatAdder(test_params.BIT_WIDTH), test_params.BIT_WIDTH)

    model.set_param(
        "top.src0.construct",
        # Input values to stream through the block in order
        msgs=[],
        # Cycles to wait after reset before starting to send inputs
        initial_delay=0,
        # Cycles to wait before sending next input (before `send_val` set high)
        interval_delay=0,
    )

    model.set_param(
        "top.src1.construct",
        # Input values to stream through the block in order
        msgs=[],
        # Cycles to wait after reset before starting to send inputs
        initial_delay=0,
        # Cycles to wait before sending next input (before `send_val` set high)
        interval_delay=0,
    )

    model.set_param(
        "top.sink.construct",
        # Expected output values to read from the block in order
        msgs=[],
        # Cycles to wait after reset before setting `recv_rdy` to high
        initial_delay=0,
        # Cycles to wait between outputs before setting `recv_rdy` to high
        interval_delay=0,
    )

    run_sim(model, cmdline_opts, duts=["comb_float_adder"])
