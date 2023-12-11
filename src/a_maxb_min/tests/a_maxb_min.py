import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.a_maxb_min.harnesses.a_maxb_min import AMaxbMin

def make_input(d, a, b):
    return (a * 2**24) + (b * 2**8)
def get_answer(d, a, b):
    alpha = 0.95703125
    beta = 0.39453125
    result = alpha * max(a,b) + beta * min(a,b)
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

def a_equals_b_test():
    return[
        make_input(8, 1, 1), get_answer(8, 1, 1),
        make_input(8, 2, 2), get_answer(8, 2, 2),
        make_input(8, 13, 13), get_answer(8, 13, 13),
        ]

def a_not_equals_b_test():
    return[
        make_input(8, 1, 2), get_answer(8, 1, 2),
        make_input(8, 2, 6), get_answer(8, 2, 6),
        make_input(8, 10, 13), get_answer(8, 10, 13),
        ]
def both_zero_test():
    return[
        make_input(8, 0, 0), get_answer(8, 0, 0)
        ]
def a_zero_test():
    return[
        make_input(8, 0, 1), get_answer(8, 0, 1),
        make_input(8, 0, 2), get_answer(8, 0, 2),
        make_input(8, 0, 13), get_answer(8, 0, 13),
    ]
def b_zero_test():
    return[
        make_input(8, 1, 0), get_answer(8, 1, 0),
        make_input(8, 2, 0), get_answer(8, 2, 0),
        make_input(8, 13, 0), get_answer(8, 13, 0),
    ]
def order_test():
    return[
        make_input(8, 1, 6), get_answer(8, 6, 1),
        make_input(8, 8, 2), get_answer(8, 2, 8),
        make_input(8, 19, 13), get_answer(8, 13, 19),
        make_input(8, 13, 19), get_answer(8, 19, 13),
    ]
def fixed_point_test():
    return[
        make_input(8, 6.1, 1), get_answer(8, 6.1, 1),
        make_input(8, 8.9, 2.11), get_answer(8, 2.11, 8.9),
        make_input(8, 19.9, 13.9), get_answer(8, 13.9, 19.9),
        make_input(8, 13.111, 19.111), get_answer(8, 19.111, 13.111),
    ]

test_case_table = mk_test_case_table(
    [
        ("msgs                          src_delay    sink_delay    BIT_WIDTH    F_BITS    slow"),
        ["a_equals_b_test", a_equals_b_test,    4,           4,            32,          16,        False],
        ["a_not_equals_b_test", a_not_equals_b_test,    4,           4,            32,          16,        False],
        ["both_zero_test", both_zero_test,    4,           4,            32,          16,        False],
        ["a_zero_test", a_zero_test,    4,           4,            32,          16,        False],
        ["b_zero_test", b_zero_test,    4,           4,            32,          16,        False],
        ["order_test", order_test,    4,           4,            32,          16,        False],
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
