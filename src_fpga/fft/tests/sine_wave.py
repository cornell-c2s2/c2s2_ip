from src.fft.helpers.sine_wave import SineWave
from pymtl3.stdlib.test_utils import run_test_vector_sim
import pytest
from tools.utils import mk_test_matrices, fixed_bits
from src.fft.sim import sine_wave


def gen_sine_wave(n_samples, bit_width, decimal_pt):

    return [
        (" ".join([f"out[{i}]*" for i in range(n_samples)])),
        [fixed_bits(x) for x in sine_wave(n_samples, bit_width, decimal_pt)],
    ]


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(8, 0), (32, 16), (32, 31), (16, 8)],
            "n_samples": [4, 8, 16, 32],
        },
        {
            "fp_spec": [(16, 8), (8, 0), (32, 16)],
            "n_samples": [128, 512],
            "slow": True,
        },
    )
)
def test(cmdline_opts, p):
    run_test_vector_sim(
        SineWave(p.n_samples, *p.fp_spec),
        gen_sine_wave(p.n_samples, *p.fp_spec),
        cmdline_opts,
    )
