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
    def construct(s, sqrt, BIT_WIDTH=32):
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


def sqrt_four():
    return [ [ 0x00000004 ], [ 0x00000002 ] ]

test_case_table = mk_test_case_table([
  (                     "msgs               src_delay  sink_delay  BIT_WIDTH "),
  [ "sqrt_four",        sqrt_four,          4,         4,          32,        ],
])

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        SqrtTestHarness(test_params.BIT_WIDTH),
        test_params.BIT_WIDTH
    )

    msgs = test_params.msgs()

    th.set_param(
        "top.src.construct",
        msgs=msgs[0],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=msgs[1],
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

    run_sim(th, cmdline_opts, duts=["sqrt"])