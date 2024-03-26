import pytest
from pymtl3 import Bits32, mk_bits
from pymtl3.stdlib.test_utils import run_test_vector_sim
from src.fft.pease.helpers.twiddle_generator import TwiddleGenerator
from src.fft.pease.sim import twiddle_generator
from src.fft.sim import sine_wave
from tools.utils import mk_test_matrices, fixed_bits, cfixed_bits
import math


def gen_twiddle(BIT_WIDTH, DECIMAL_PT, SIZE_FFT, STAGE_FFT):
    return [
        (
            " ".join(
                [f"sine_wave_in[{i}]" for i in range(SIZE_FFT)]
                + [f"twiddle_real[{i}]" for i in range(SIZE_FFT // 2)]
                + [f"twiddle_imaginary[{i}]" for i in range(SIZE_FFT // 2)]
            )
        ),
        [fixed_bits(x) for x in sine_wave(SIZE_FFT, BIT_WIDTH, DECIMAL_PT)]
        + sum(
            list(
                map(
                    list,
                    zip(
                        *[
                            cfixed_bits(x)
                            for x in twiddle_generator(
                                BIT_WIDTH, DECIMAL_PT, SIZE_FFT, STAGE_FFT
                            )
                        ]
                    ),
                )
            ),
            [],
        ),
    ]


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16), (32, 31), (16, 8)],
            "n_samples": [8, 32],
        },
        {
            "fp_spec": [(32, 16), (8, 0)],
            "n_samples": [256, 512],
            "slow": True,
        },
    )
)
def test(cmdline_opts, p):
    for stage in range(0, int(math.log2(p.n_samples))):
        run_test_vector_sim(
            TwiddleGenerator(*p.fp_spec, p.n_samples, stage),
            gen_twiddle(*p.fp_spec, p.n_samples, stage),
            cmdline_opts,
        )
