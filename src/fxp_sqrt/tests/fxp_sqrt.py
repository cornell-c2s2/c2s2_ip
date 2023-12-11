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
def simple_test():
    return [
        0xE890, 0x0F40, 
        0x0040, 0x0080, 
        0x0200, 0x016A, 
        256, 256]

def int_perfect_squares_8bit():
    return [
        make_fixed(8, 4, 0), math.sqrt(0)*16,
        make_fixed(8, 4, 1), math.sqrt(1)*16,
        make_fixed(8, 4, 4), math.sqrt(4)*16,
        make_fixed(8, 4, 9), math.sqrt(9)*16,
    ]

def int_perfect_squares_16bit():
    return [
        make_fixed(16, 8, 0), math.sqrt(0)*256,
        make_fixed(16, 8, 1), math.sqrt(1)*256,
        make_fixed(16, 8, 4), math.sqrt(4)*256,
        make_fixed(16, 8, 9), math.sqrt(9)*256,
        make_fixed(16, 8, 16), math.sqrt(16)*256,
        make_fixed(16, 8, 25), math.sqrt(25)*256,
        make_fixed(16, 8, 36), math.sqrt(36)*256,
        make_fixed(16, 8, 49), math.sqrt(49)*256,
        make_fixed(16, 8, 64), math.sqrt(64)*256,
        make_fixed(16, 8, 81), math.sqrt(81)*256,
        make_fixed(16, 8, 100), math.sqrt(100)*256,
        make_fixed(16, 8, 225), math.sqrt(225)*256,
    ]

def int_perfect_squares_32bit():
    return [
        make_fixed(32, 16, 0), math.sqrt(0)*65536,
        make_fixed(32, 16, 1), math.sqrt(1)*65536,
        make_fixed(32, 16, 4), math.sqrt(4)*65536,
        make_fixed(32, 16, 9), math.sqrt(9)*65536,
        make_fixed(32, 16, 16), math.sqrt(16)*65536,
        make_fixed(32, 16, 25), math.sqrt(25)*65536,
        make_fixed(32, 16, 36), math.sqrt(36)*65536,
        make_fixed(32, 16, 49), math.sqrt(49)*65536,
        make_fixed(32, 16, 64), math.sqrt(64)*65536,
        make_fixed(32, 16, 81), math.sqrt(81)*65536,
        make_fixed(32, 16, 100), math.sqrt(100)*65536,
        make_fixed(32, 16, 58081), math.sqrt(58081)*65536,
        make_fixed(32, 16, 58564), math.sqrt(58564)*65536,
        make_fixed(32, 16, 59049), math.sqrt(59049)*65536,
        make_fixed(32, 16, 59536), math.sqrt(59536)*65536,
        make_fixed(32, 16, 60025), math.sqrt(60025)*65536,
        make_fixed(32, 16, 60516), math.sqrt(60516)*65536,
        make_fixed(32, 16, 61009), math.sqrt(61009)*65536,
        make_fixed(32, 16, 61504), math.sqrt(61504)*65536,
        make_fixed(32, 16, 62001), math.sqrt(62001)*65536,
        make_fixed(32, 16, 62500), math.sqrt(62500)*65536,
        make_fixed(32, 16, 62951), math.sqrt(62951)*65536,
        make_fixed(32, 16, 63504), math.sqrt(63504)*65536,
        make_fixed(32, 16, 64009), math.sqrt(64009)*65536,
        make_fixed(32, 16, 64516), math.sqrt(64516)*65536,
        make_fixed(32, 16, 65025), math.sqrt(65025)*65536,
        make_fixed(32, 16, 65025), math.sqrt(65025)*65536,
    ]

def fxp_8bit(n=8, d=4):
    list = []
    for i in range(50):
        rand_fxp_num = rand_fxp(n,d)
        list.append(make_fixed(n, d, rand_fxp_num))
        list.append(math.sqrt(rand_fxp_num)*(2**d))
    return list

def fxp_16bit(n=16, d=8):
    list = []
    for i in range(50):
        rand_fxp_num = rand_fxp(n,d)
        list.append(make_fixed(n, d, rand_fxp_num))
        list.append(math.sqrt(rand_fxp_num)*(2**d))
    return list

def fxp_32bit(n=32, d=16):
    list = []
    for i in range(50):
        rand_fxp_num = rand_fxp(n,d)
        list.append(make_fixed(n, d, rand_fxp_num))
        list.append(math.sqrt(rand_fxp_num)*(2**d))
    return list

def simple_test_delay_recv_fast():
    return [
        0xE890, 0x0F40, 
        0x0040, 0x0080, 
        0x0200, 0x016A, 
        256, 256]

def simple_test_delay_send_fast():
    return [
        0xE890, 0x0F40, 
        0x0040, 0x0080, 
        0x0200, 0x016A, 
        256, 256]

def simple_test_delay_recv_slow():
    return [
        0xE890, 0x0F40, 
        0x0040, 0x0080, 
        0x0200, 0x016A, 
        256, 256]

def simple_test_delay_send_slow():
    return [
        0xE890, 0x0F40, 
        0x0040, 0x0080, 
        0x0200, 0x016A, 
        256, 256]

test_case_table = mk_test_case_table(
    [
        (
            "msgs                                          src_delay sink_delay BIT_WIDTH F_BITS slow"
        ),
        ["simple_test", simple_test, 4, 4, 16, 8, False],
        ["int_perfect_squares_8bit", int_perfect_squares_8bit, 4, 4, 8, 4, False],
        ["int_perfect_squares_16bit", int_perfect_squares_16bit, 4, 4, 16, 8, False],
        ["int_perfect_squares_32bit", int_perfect_squares_32bit, 4, 4, 32, 16, False],
        ["fxp_8bit", fxp_8bit, 4, 4, 8, 4, False],
        ["fxp_16bit", fxp_16bit, 4, 4, 16, 8, False],
        ["fxp_32bit", fxp_32bit, 4, 4, 32, 16, False],
        ["simple_test_delay_recv_fast", simple_test_delay_recv_fast, 2, 4, 16, 8, False],
        ["simple_test_delay_send_fast", simple_test_delay_send_fast, 4, 2, 16, 8, False],
        ["simple_test_delay_recv_slow", simple_test_delay_recv_slow, 6, 4, 16, 8, False],
        ["simple_test_delay_send_slow", simple_test_delay_send_slow, 4, 6, 16, 8, False],
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
