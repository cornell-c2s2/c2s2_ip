# =========================================================================
# Sqrt_test
# =========================================================================

import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.sqrt.harnesses.sqrt import SqrtTestHarness

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
    return [
        0x04,
        0x02,
        0x09,
        0x03,
        0x10,
        0x04,
        0x19,
        0x05,
        0x24,
        0x06,
        0x31,
        0x07,
        0x40,
        0x08,
        0x51,
        0x09,
        0x64,
        0x0A,
        0x79,
        0x0B,
    ]


test_case_table = mk_test_case_table(
    [
        ("msgs src_delay sink_delay BIT_WIDTH "),
        [
            "perfect_squares",
            perfect_squares,
            4,
            4,
            8,
        ],
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
