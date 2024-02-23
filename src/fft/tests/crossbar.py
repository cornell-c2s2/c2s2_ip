from src.fft.helpers.crossbar import Crossbar
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3 import mk_bits
import pytest
import math
import random
from tools.utils import mk_test_matrices, cfixed_bits, fixed_bits
from fixedpt import Fixed, CFixed


# front crossbar (set FRONT = 1 in verilog model)
def crossbar_front(
    n_samples: int, stage_fft: int, cbar_in: list[CFixed]
) -> list[CFixed]:
    cbar_out = [None for _ in range(n_samples)]

    for m in range(0, 2**stage_fft):
        for i in range(m, n_samples, 2 ** (stage_fft + 1)):
            cbar_out[i + m] = cbar_in[i]
            cbar_out[i + m + 1] = cbar_in[i + 2**stage_fft]

    return cbar_out


# back crossbar (set FRONT = 0 in verilog model)
def crossbar_back(
    n_samples: int, stage_fft: int, cbar_in: list[CFixed]
) -> list[CFixed]:
    cbar_out = [None for _ in range(n_samples)]

    for m in range(0, 2**stage_fft):
        for i in range(m, n_samples, 2 ** (stage_fft + 1)):
            cbar_out[i] = cbar_in[i + m]
            cbar_out[i + 2**stage_fft] = cbar_in[i + m + 1]

    return cbar_out


# get output of crossbar_front
def gen_crossbar_front(stage_fft, n_samples, cbar_in):
    return [
        (" ".join([f"out[{i}]*" for i in range(n_samples)])),
        [fixed_bits(x) for x in crossbar_front(stage_fft, n_samples, cbar_in)],
    ]


# get output of crossbar_back
def gen_crossbar_back(stage_fft, n_samples, cbar_in):
    return [
        (" ".join([f"out[{i}]*" for i in range(n_samples)])),
        [fixed_bits(x) for x in crossbar_back(stage_fft, n_samples, cbar_in)],
    ]


# generate a random CFixed value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )


# generate a list of random CFixed values
def input_gen(bit_width, decimal_pt, n_samples) -> list[CFixed]:
    return [rand_cfixed(bit_width, decimal_pt) for i in range(n_samples)]


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16), (32, 31), (32, 24)],
            "n_samples": [8, 32, 256, 512],
        }
    )
)
def test_front(cmdline_opts, p):
    for stage in range(0, int(math.log2(p.n_samples))):
        run_test_vector_sim(
            Crossbar(*p.fp_spec, p.n_samples, stage),
            gen_crossbar_front(p.n_samples, stage, input_gen(*p.fp_spec, p.n_samples)),
            cmdline_opts,
        )


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16), (32, 31), (32, 24)],
            "n_samples": [8, 32, 256, 512],
        }
    )
)
def test_back(cmdline_opts, p):
    for stage in range(0, int(math.log2(p.n_samples))):
        run_test_vector_sim(
            Crossbar(*p.fp_spec, p.n_samples, stage),
            gen_crossbar_back(p.n_samples, stage, input_gen(*p.fp_spec, p.n_samples)),
            cmdline_opts,
        )
