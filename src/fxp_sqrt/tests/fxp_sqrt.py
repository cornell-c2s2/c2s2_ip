# =========================================================================
# Fxp_sqrt_test
# =========================================================================

import pytest
import random
import math
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.fxp_sqrt.harnesses.fxp_sqrt import FxpSqrtTestHarness

# ----------------------------------------------------------------------
# Helper Functions
# ----------------------------------------------------------------------
def make_fixed (n, d, a, b):
    return (a << d) + b

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


class TestHarness(Component):
    def construct(s, fxp_sqrt, BIT_WIDTH=32, F_BITS=16):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.fxp_sqrt = fxp_sqrt

        # Connect

        s.src.send //= s.fxp_sqrt.recv
        s.fxp_sqrt.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# ----------------------------------------------------------------------
# Test Case Table
# ----------------------------------------------------------------------
def five():
    return [make_fixed(16, 8, 2, 0),math.sqrt(2)*256]

def simple_test():
    return [
        0xE890, 0x0F40, 
        0x0040, 0x0080, 
        0x0200, 0x016A, 
        256, 256]

def int_perfect_squares_8bit():
    return [
        make_fixed(8, 4, 0, 0), math.sqrt(0)*16,
        make_fixed(8, 4, 1, 0), math.sqrt(1)*16,
        make_fixed(8, 4, 4, 0), math.sqrt(4)*16,
        make_fixed(8, 4, 9, 0), math.sqrt(9)*16,
    ]

def int_perfect_squares_16bit():
    return [
        make_fixed(16, 8, 0, 0), math.sqrt(0)*256,
        make_fixed(16, 8, 1, 0), math.sqrt(1)*256,
        make_fixed(16, 8, 4, 0), math.sqrt(4)*256,
        make_fixed(16, 8, 9, 0), math.sqrt(9)*256,
        make_fixed(16, 8, 16, 0), math.sqrt(16)*256,
        make_fixed(16, 8, 25, 0), math.sqrt(25)*256,
        make_fixed(16, 8, 36, 0), math.sqrt(36)*256,
        make_fixed(16, 8, 49, 0), math.sqrt(49)*256,
        make_fixed(16, 8, 64, 0), math.sqrt(64)*256,
        make_fixed(16, 8, 81, 0), math.sqrt(81)*256,
        make_fixed(16, 8, 100, 0), math.sqrt(100)*256,
        make_fixed(16, 8, 225, 0), math.sqrt(225)*256,
    ]

def int_perfect_squares_32bit():
    return [
        make_fixed(32, 16, 0, 0), math.sqrt(0)*65536,
        make_fixed(32, 16, 1, 0), math.sqrt(1)*65536,
        make_fixed(32, 16, 4, 0), math.sqrt(4)*65536,
        make_fixed(32, 16, 9, 0), math.sqrt(9)*65536,
        make_fixed(32, 16, 16, 0), math.sqrt(16)*65536,
        make_fixed(32, 16, 25, 0), math.sqrt(25)*65536,
        make_fixed(32, 16, 36, 0), math.sqrt(36)*65536,
        make_fixed(32, 16, 49, 0), math.sqrt(49)*65536,
        make_fixed(32, 16, 64, 0), math.sqrt(64)*65536,
        make_fixed(32, 16, 81, 0), math.sqrt(81)*65536,
        make_fixed(32, 16, 100, 0), math.sqrt(100)*65536,
        make_fixed(32, 16, 58081, 0), math.sqrt(58081)*65536,
        make_fixed(32, 16, 58564, 0), math.sqrt(58564)*65536,
        make_fixed(32, 16, 59049, 0), math.sqrt(59049)*65536,
        make_fixed(32, 16, 59536, 0), math.sqrt(59536)*65536,
        make_fixed(32, 16, 60025, 0), math.sqrt(60025)*65536,
        make_fixed(32, 16, 60516, 0), math.sqrt(60516)*65536,
        make_fixed(32, 16, 61009, 0), math.sqrt(61009)*65536,
        make_fixed(32, 16, 61504, 0), math.sqrt(61504)*65536,
        make_fixed(32, 16, 62001, 0), math.sqrt(62001)*65536,
        make_fixed(32, 16, 62500, 0), math.sqrt(62500)*65536,
        make_fixed(32, 16, 62951, 0), math.sqrt(62951)*65536,
        make_fixed(32, 16, 63504, 0), math.sqrt(63504)*65536,
        make_fixed(32, 16, 64009, 0), math.sqrt(64009)*65536,
        make_fixed(32, 16, 64516, 0), math.sqrt(64516)*65536,
        make_fixed(32, 16, 65025, 0), math.sqrt(65025)*65536,
        make_fixed(32, 16, 65025, 0), math.sqrt(65025)*65536,
    ]

def fxp_perfect_squares_16bit():
    return [
        0x0002, math.sqrt(0.00390625)*256,
    ]

test_case_table = mk_test_case_table(
    [
        (
            "msgs                                          src_delay sink_delay BIT_WIDTH F_BITS slow"
        ),
        ["simple_test", simple_test, 4, 4, 16, 8, False],
        ["int_perfect_squares_8bit", int_perfect_squares_8bit, 4, 4, 8, 4, False],
        ["int_perfect_squares_16bit", int_perfect_squares_16bit, 4, 4, 16, 8, False],
        ["int_perfect_squares_32bit", int_perfect_squares_32bit, 4, 4, 32, 16, False],
        ["five", five, 4, 4, 16, 8, False],
        #["fxp_perfect_squares_16bit", fxp_perfect_squares_16bit, 4, 4, 16, 8, False]
    ]
)

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        FxpSqrtTestHarness(test_params.BIT_WIDTH, test_params.F_BITS),
        test_params.BIT_WIDTH,
        test_params.F_BITS,
    )

    msgs = test_params.msgs()

    th.set_param(
        "top.src.construct",
        msgs=msgs[::2],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=msgs[1::2],
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

    run_sim(th, cmdline_opts, duts=["fxp_sqrt"])
