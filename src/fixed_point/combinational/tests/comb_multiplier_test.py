# =========================================================================
# IntMulStep_test
# =========================================================================

import pytest
import struct
from pymtl3.stdlib.test_utils import run_test_vector_sim
from random import randint, seed
import decimal

from src.fixed_point.combinational.harnesses.FpCombMultVRTL import FpCombMultVRTL
from fixedpt import Fixed


def simple_case():
    test_cases = [("a b c* ")]
    test_cases.append([0x00010000, 0x00010000, 0x00010000])
    return test_cases


def rand_fixed(n, d):
    return Fixed(randint(0, (1 << n) - 1), 1, n, d, raw=True)


def gen_random_test_case(n, d, num):
    test_cases = [("a b c* ")]
    for i in range(num):
        a = rand_fixed(n, d)
        b = rand_fixed(n, d)
        c = (a * b).resize(None, n, d)
        test_cases.append([a.get(), b.get(), c.get()])
    return test_cases


def test_simple(cmdline_opts):
    run_test_vector_sim(FpCombMultVRTL(32, 16, 1), simple_case(), cmdline_opts)


def test_random(n, d):
    run_test_vector_sim(
        FpCombMultVRTL(n, d, 1), gen_random_test_case(n, d, 100), cmdline_opts
    )


def test_random_i32_16(cmdline_opts):
    run_test_vector_sim(
        FpCombMultVRTL(32, 16, 1), gen_random_test_case(32, 16, 100), cmdline_opts
    )


# Merge a and b into a larger number
def mk_msg(n, a, b):
    return (a << n) | b


# Create test parametrization information
def mk_params(execution_number, sequence_lengths, n, d):
    if isinstance(n, int):
        n = (n, n)
    if isinstance(d, int):
        d = (d, d)

    return [(j, i, n, d) for i in sequence_lengths for j in range(execution_number)]


@pytest.mark.parametrize(
    "n, d, a, b",
    [
        (3, 0, 3, 3),  # overflow check
        (2, 1, 0.5, -0.5),
        (6, 3, -4, -0.125),  # 100.000 * 111.111 = 000.100
        (6, 3, 3.875, -0.125),  # -0.375
    ],
)
def test_edge(n, d, a, b):
    a = Fixed(a, 1, n, d)
    b = Fixed(b, 1, n, d)
    c = (a * b).resize(None, n, d)

    test_case = [("a b c* ")]
    test_case.append([a.get(), b.get(), c.get()])

    run_test_vector_sim(FpCombMultVRTL(n, d, 1), test_case, cmdline_opts={})


@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d",
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(20, [1, 10, 50, 100], (16, 64), (0, 64)) +
    # Extensively tests numbers with certain important bit sizes.
    sum(
        [
            mk_params(1, [1, 100, 1000], n, d)
            for (n, d) in [
                (8, 4),
                (24, 8),
                (32, 24),
                (32, 16),
                (64, 32),
            ]
        ],
        [],
    ),
)
def test_random(
    execution_number, sequence_length, n, d
):  # test individual and sequential multiplications to assure stream system works
    n = randint(n[0], n[1])
    d = randint(d[0], min(n - 1, d[1]))  # decimal bits

    test_cases = [("a b c* ")]

    for i in range(sequence_length):
        a = rand_fixed(n, d)
        b = rand_fixed(n, d)
        c = (a * b).resize(None, n, d)
        test_cases.append([a.get(), b.get(), c.get()])

    run_test_vector_sim(FpCombMultVRTL(n, d, 1), test_cases, cmdline_opts={})
