import pytest
import random
import math
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.distance_cal.harnesses.distance_cal import DCalTestHarness
from fixedpt import Fixed 
from tools.pymtl_extensions import mk_packed

# ----------------------------------------------------------------------
# Helper Functions
# ----------------------------------------------------------------------
def make_fixed (n, d, a):
    max_fraction_value = 2**d
    scaled_number = round(a * max_fraction_value)
    binary_representation = bin(scaled_number & int("1" * n, 2))[2:]
    return int(binary_representation.zfill(n),2)

def rand_fxp (n, d):
    integer_bits = n - d  
    int_max = 2 ** integer_bits - 1
    integer_part = random.randint(0, int_max)
    fractional_max = 2 ** d - 1
    fractional_part = random.randint(0, fractional_max) / 2 ** d
    random_float = float(integer_part) + fractional_part
    return random_float

def dist(a, b):
    return math.sqrt(a**2 + b**2)

# Merge a and b into a single bus
def mk_msg(n, a, b):
    return mk_packed(n)(a, b)

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, distance_cal, BIT_WIDTH=32, F_BITS=16):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(2*BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.distance_cal = distance_cal

        # Connect

        s.src.send //= s.distance_cal.recv
        s.distance_cal.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

def both_zero():
    return [mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 0)), dist(0,0)*15]

def in_same_out():
    return [mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 2.5)),dist(0,2.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 0.5)), dist(0,0.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 1)), dist(0,1)*16,
            mk_msg(8, make_fixed(8, 4, 2.1), make_fixed(8, 4, 0)), dist(0,2.1)*16,
            mk_msg(8, make_fixed(8, 4, 2.5), make_fixed(8, 4, 0)), dist(0,2.5)*16,
            mk_msg(8, make_fixed(8, 4, 0.5), make_fixed(8, 4, 0)), dist(0,0.5)*16,
            mk_msg(8, make_fixed(8, 4, 1), make_fixed(8, 4, 0)), dist(0,1)*16,
            mk_msg(8, make_fixed(8, 4, 2.1), make_fixed(8, 4, 0)), dist(0,2.1)*16
            ]

def fxp_8bit(n=8, d=4):
    list = []
    for i in range(50):
        rand_fxp_num1 = rand_fxp(n,d)
        rand_fxp_num2 = rand_fxp(n,d)
        list.append(mk_msg(n, make_fixed(n, d, rand_fxp_num1), make_fixed(n, d, rand_fxp_num2)))
        list.append((dist(rand_fxp_num1,rand_fxp_num2))*(2**d))
    return list

def fxp_16bit(n=16, d=8):
    list = []
    for i in range(50):
        rand_fxp_num1 = rand_fxp(n,d)
        rand_fxp_num2 = rand_fxp(n,d)
        list.append(mk_msg(n, make_fixed(n, d, rand_fxp_num1), make_fixed(n, d, rand_fxp_num2)))
        list.append((dist(rand_fxp_num1,rand_fxp_num2))*(2**d))
    return list

def fxp_32bit(n=32, d=16):
    list = []
    for i in range(50):
        rand_fxp_num1 = rand_fxp(n,d)
        rand_fxp_num2 = rand_fxp(n,d)
        list.append(mk_msg(n, make_fixed(n, d, rand_fxp_num1), make_fixed(n, d, rand_fxp_num2)))
        list.append((dist(rand_fxp_num1,rand_fxp_num2))*(2**d))
    return list

def simple_test_delay_recv_fast():
    return [mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 2.5)),dist(0,2.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 0.5)), dist(0,0.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 1)), dist(0,1)*16,
            mk_msg(8, make_fixed(8, 4, 2.1), make_fixed(8, 4, 0)), dist(0,2.1)*16]

def simple_test_delay_send_fast():
    return [mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 2.5)),dist(0,2.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 0.5)), dist(0,0.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 1)), dist(0,1)*16,
            mk_msg(8, make_fixed(8, 4, 2.1), make_fixed(8, 4, 0)), dist(0,2.1)*16]

def simple_test_delay_recv_slow():
    return [mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 2.5)),dist(0,2.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 0.5)), dist(0,0.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 1)), dist(0,1)*16,
            mk_msg(8, make_fixed(8, 4, 2.1), make_fixed(8, 4, 0)), dist(0,2.1)*16]

def simple_test_delay_send_slow():
    return [mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 2.5)),dist(0,2.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 0.5)), dist(0,0.5)*16,
            mk_msg(8, make_fixed(8, 4, 0), make_fixed(8, 4, 1)), dist(0,1)*16,
            mk_msg(8, make_fixed(8, 4, 2.1), make_fixed(8, 4, 0)), dist(0,2.1)*16]


test_case_table = mk_test_case_table(
    [
        (
            "msgs                          src_delay    sink_delay    BIT_WIDTH    F_BITS    slow"
        ),
        ["both_zero", both_zero, 4, 4, 8, 4, False],
        ["in_same_out", in_same_out, 4, 4, 8, 4, False],
        ["fxp_8bit", fxp_8bit, 4, 4, 8, 4, False],
        ["fxp_8bit", fxp_8bit, 4, 4, 8, 4, False],
        ["fxp_16bit", fxp_16bit, 4, 4, 16, 8, False],
        ["fxp_32bit", fxp_32bit, 4, 4, 32, 16, False],
        ["simple_test_delay_recv_fast", simple_test_delay_recv_fast, 2, 4, 8, 4, False],
        ["simple_test_delay_send_fast", simple_test_delay_send_fast, 4, 2, 8, 4, False],
        ["simple_test_delay_recv_slow", simple_test_delay_recv_slow, 6, 4, 8, 4, False],
        ["simple_test_delay_send_slow", simple_test_delay_send_slow, 4, 6, 8, 4, False],
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
