import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.a_maxb_min.harnesses.a_maxb_min import AMaxbMin


def make_input(d, a, b):
    return (a << 24) + (b << 8)


def get_answer(d, a, b):
    alpha = 0.95703125
    beta = 0.39453125
    result = alpha * max(a, b) + beta * min(a, b)
    return (int)(result * 2**d)


class TestHarness(Component):
    def construct(s, a_maxb_min, BIT_WIDTH=32, F_BITS=16):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.a_maxb_min = a_maxb_min

        # Connect

        s.src.send //= s.a_maxb_min.recv
        s.a_maxb_min.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


def simple_test():
    return [2, 2]


test_case_table = mk_test_case_table(
    [
        (
            "msgs                          src_delay    sink_delay    BIT_WIDTH    F_BITS    slow"
        ),
        ["simple_test", simple_test, 4, 4, 32, 16, False],
    ]
)


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        AMaxbMin(test_params.BIT_WIDTH, test_params.F_BITS),
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

    run_sim(th, cmdline_opts, duts=["a_maxb_min"])
