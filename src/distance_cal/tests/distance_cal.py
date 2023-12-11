import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.distance_cal.harnesses.distance_cal import DCalTestHarness

class TestHarness(Component):
    def construct(s, distance_cal, BIT_WIDTH=32, F_BITS=16):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.distance_cal = distance_cal

        # Connect

        s.src.send //= s.distance_cal.recv
        s.distance_cal.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


def simple_test():
    return [0x20, 0x20]


test_case_table = mk_test_case_table(
    [
        (
            "msgs                          src_delay    sink_delay    BIT_WIDTH    F_BITS    slow"
        ),
        ["simple_test", simple_test, 4, 4, 8, 4, False],
    ]
)


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        DCalTestHarness(test_params.BIT_WIDTH, test_params.F_BITS),
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

    run_sim(th, cmdline_opts, duts=["distance_cal"])
