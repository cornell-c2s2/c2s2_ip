from pymtl3 import *
from pymtl3.stdlib.test_utils import run_test_vector_sim
from src.fft.cooley_tukey.harnesses.twiddle_generator import TwiddleGenerator


# 8 point FFT, stage 0
# Expects 1, 1, 1, 1
def test_small(cmdline_opts):
    run_test_vector_sim(
        TwiddleGenerator(4, 1, 8, 0),
        [
            ("send_msg*"),
            [0x22220000],
        ],
        cmdline_opts,
    )


# 8 point FFT, stage 1
# Expects 1, -i, 1, -i
# Matches 2 + 0j, 0 + Ej, 2 + 0j, 0 + Ej
def test_small_2(cmdline_opts):
    run_test_vector_sim(
        TwiddleGenerator(4, 1, 8, 1),
        [
            ("send_msg*"),
            [0x0202E0E0],
        ],
        cmdline_opts,
    )


# 8 point FFT, stage 2
# Expects -1, sqrt(2) - isqrt(2), -i, -sqrt(2) - sqrt(2)
def test_small_3(cmdline_opts):
    run_test_vector_sim(
        TwiddleGenerator(32, 16, 8, 2),
        [
            ("send_msg*"),
            [0xFFFF4AFC_00000000_0000B504_00010000_FFFF4AFC_FFFF0000_FFFF4AFC_00000000],
        ],
        cmdline_opts,
    )


def test_small_4(cmdline_opts):
    run_test_vector_sim(
        TwiddleGenerator(32, 16, 4, 0),
        [
            ("send_msg*"),
            [0x00010000_00010000_00000000_00000000],
        ],
        cmdline_opts,
    )


def test_small_5(cmdline_opts):
    run_test_vector_sim(
        TwiddleGenerator(32, 16, 4, 1),
        [
            ("send_msg*"),
            [0x00000000_00010000_FFFF0000_00000000],
        ],
        cmdline_opts,
    )
