# =========================================================================
# Sqrt_test
# =========================================================================

import pytest
import random
import math
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.sqrt.harnesses.sqrt import SqrtTestHarness


# ----------------------------------------------------------------------
# Helper Functions
# ----------------------------------------------------------------------
def isPerfectSquare(n):
    return n == round(math.sqrt(n)) ** 2


def lastPerfectSquare(n):
    while not isPerfectSquare(n):
        n = n - 1
    return round(math.sqrt(n))


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


class TestHarness(Component):
    def construct(s, sqrt, BIT_WIDTH=8):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.sqrt = sqrt

        # Connect

        s.src.send //= s.sqrt.recv
        s.sqrt.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# ----------------------------------------------------------------------
# Test Case Table
# ----------------------------------------------------------------------
def perfect_squares():
    RANGE = 255
    i, list = 0, []
    while i <= RANGE:
        if isPerfectSquare(i):
            list.append(i)
            list.append(int(math.sqrt(i)))
        i = i + 1
    print(list)
    return list


def non_perfect_squares():
    RANGE = 255
    i, list = 0, []
    while i <= RANGE:
        if not isPerfectSquare(i):
            list.append(i)
            list.append(lastPerfectSquare(i))
        i = i + 1
    print(list)
    return list


test_case_table = mk_test_case_table(
    [
        (
            "msgs                                          src_delay sink_delay BIT_WIDTH "
        ),
        ["perfect_squares", perfect_squares, 4, 4, 8],
        ["non_perfect_squares", non_perfect_squares, 4, 4, 8],
    ]
)

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(SqrtTestHarness(test_params.BIT_WIDTH), test_params.BIT_WIDTH)

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

    run_sim(th, cmdline_opts, duts=["sqrt"])
