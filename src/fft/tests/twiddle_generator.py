from src.fft.helpers.twiddle_generator import TwiddleGenerator
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3 import mk_bits
import pytest
import math
from tools.utils import mk_test_matrices, cfixed_bits, fixed_bits
from fixedpt import Fixed, CFixed
from src.fft.tests.sine_wave import sine_wave


def twiddle_generator(
    BIT_WIDTH: int, DECIMAL_PT: int, SIZE_FFT: int, STAGE_FFT: int
) -> list[CFixed]:
    sine_wave_in = sine_wave(SIZE_FFT, BIT_WIDTH, DECIMAL_PT)
    twiddles = [0] * (SIZE_FFT // 2)

    for m in range(0, 2**STAGE_FFT):
        for i in range(0, SIZE_FFT, 2 ** (STAGE_FFT + 1)):
            idx = m * SIZE_FFT / (1 << (STAGE_FFT + 1))
            twiddles[(i // 2) + m] = CFixed(
                (
                    sine_wave_in[int((idx + SIZE_FFT / 4) % SIZE_FFT)],
                    -sine_wave_in[int(idx % SIZE_FFT)],
                ),
                BIT_WIDTH,
                DECIMAL_PT,
            )

    return twiddles


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
            "fp_spec": [(32, 16), (32, 31), (32, 24)],
            "n_samples": [8, 32, 256, 512],
        }
    )
)
def test(cmdline_opts, p):
    for stage in range(0, int(math.log2(p.n_samples))):
        run_test_vector_sim(
            TwiddleGenerator(*p.fp_spec, p.n_samples, stage),
            gen_twiddle(*p.fp_spec, p.n_samples, stage),
            cmdline_opts,
        )
