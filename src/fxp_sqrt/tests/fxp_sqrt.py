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
def isPerfectSquare(n): return (n == round(math.sqrt(n)) ** 2)
def lastPerfectSquare(n):
    while(not isPerfectSquare(n)):n = n - 1
    return round(math.sqrt(n))


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


class TestHarness(Component):
    def construct(s, fxp_sqrt, BIT_WIDTH=16, F_BITS=8):
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
def simple_test():
    return [
        0xE890, 0x0F40, 
        0x0040, 0x0080, 
        0x0200, 0x016A, 
        256, 256]
    
def whole_number_perfect_squares():
    RANGE = 255
    i, list  = 0, []
    while(i <= RANGE):
        if(isPerfectSquare(i)):
            list.append(i * 256)
            list.append(int(math.sqrt(i) * 256))
        i = i + 1
    return list

def whole_number_non_perfect_squares():
    RANGE = 255
    i, list  = 0, []
    while(i <= RANGE):
        if(not isPerfectSquare(i)):
            list.append(i * 256)
            list.append(math.sqrt(i) * 256)
        i = i + 1
    return list

def fixed_point_test():
    RANGE = 255
    NUMRANDTESTS = 10
    i, list  = 0, []
    for i in range(NUMRANDTESTS):
        r = random.random() * 255
        list.append(r * 256)
        list.append(math.sqrt(r) * 256)
        i = i + 1
    return list


test_case_table = mk_test_case_table(
    [
        (
            "msgs                                          src_delay sink_delay BIT_WIDTH F_BITS"
        ),
        ["simple_test", simple_test, 4, 4, 16, 8],
        ["perfect_squares", whole_number_perfect_squares, 4, 4, 16, 8],
        ["non_perfect_squares", whole_number_non_perfect_squares, 4, 4, 16, 8],
        ["fixed_point_tests", fixed_point_test, 4, 4, 16, 8],
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
