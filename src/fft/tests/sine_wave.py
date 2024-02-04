from src.fft.helpers.sine_wave import SineWave
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3 import mk_bits
import pytest
import math
from tools.utils import mk_test_matrices


def gen_sine_wave(n_samples, bit_width, decimal_pt):
    bits = mk_bits(bit_width)

    return [
        (" ".join([f"out[{i}]*" for i in range(n_samples)])),
        [
            bits(round((math.sin(2 * math.pi * i / n_samples)) * (1 << decimal_pt)))
            for i in range(n_samples)
        ],
    ]


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16), (32, 31), (32, 24)],
            "n_samples": [4, 8, 16, 32, 128, 256, 512],
        }
    )
)
def test(cmdline_opts, p):
    run_test_vector_sim(
        SineWave(p.n_samples, *p.fp_spec),
        gen_sine_wave(p.n_samples, *p.fp_spec),
        cmdline_opts,
    )
