from fixedpt import CFixed
from src.fft.sim import sine_wave, bit_reverse
import math


def stride_permutation(n_samples: int, cbar_in: list[any]) -> list[any]:
    assert len(cbar_in) == n_samples
    return [
        *[cbar_in(i * 2) for i in range(n_samples // 2)],
        *[cbar_in(i * 2 + 1) for i in range(n_samples // 2)],
    ]


# Twiddle factor generator
def twiddle_generator(
    BIT_WIDTH: int, DECIMAL_PT: int, SIZE_FFT: int, STAGE_FFT: int
) -> list[CFixed]:
    sine_wave_in = sine_wave(SIZE_FFT, BIT_WIDTH, DECIMAL_PT)
    twiddles = [0] * (SIZE_FFT // 2)

    for m in range(0, 2**STAGE_FFT):
        twiddle_idx = (
            m * SIZE_FFT / (1 << (STAGE_FFT + 1))
        )  # Which twiddle factor to use
        for i in range(0, (SIZE_FFT // 2 ** (STAGE_FFT + 1))):  # 2**(nstages-stage-1)
            twiddles[m + i] = CFixed(
                (
                    sine_wave_in[(twiddle_idx + SIZE_FFT // 4) % SIZE_FFT],  # cos
                    sine_wave_in[(twiddle_idx + SIZE_FFT // 2) % SIZE_FFT],  # -sin
                ),
                BIT_WIDTH,
                DECIMAL_PT,
            )

    return twiddles


def fft(
    fft_in: list[CFixed], bit_width: int, decimal_pt: int, n_samples: int
) -> list[CFixed]:
    # Bit reverse the input
    data = bit_reverse(fft_in, n_samples)

    n_stages = int(math.log2(n_samples))
