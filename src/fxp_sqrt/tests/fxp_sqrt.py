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
    return [0xE890, 0x0F40, 0x0040, 0x0080, 0x0200, 0x016A]


test_case_table = mk_test_case_table(
    [
        (
            "msgs                                          src_delay sink_delay BIT_WIDTH F_BITS"
        ),
        ["simple_test", simple_test, 4, 4, 16, 8],
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
