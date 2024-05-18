from fixedpt import CFixed
from src.fft.sim import sine_wave, bit_reverse
from src.fixed_point.sim import butterfly
import math


def stride_permutation(n_samples: int, cbar_in: list[any]) -> list[any]:
    assert len(cbar_in) == n_samples
    return [
        *[cbar_in[i * 2] for i in range(n_samples // 2)],
        *[cbar_in[i * 2 + 1] for i in range(n_samples // 2)],
    ]


# Twiddle factor generator
def twiddle_generator(
    BIT_WIDTH: int, DECIMAL_PT: int, SIZE_FFT: int, STAGE_FFT: int
) -> list[CFixed]:
    sine_wave_in = sine_wave(SIZE_FFT, BIT_WIDTH, DECIMAL_PT)
    twiddles = [None] * (SIZE_FFT // 2)

    chunk_size = int(SIZE_FFT / (1 << (STAGE_FFT + 1)))

    for m in range(0, 2**STAGE_FFT):
        twiddle_idx = m * chunk_size  # Which twiddle factor to use
        for i in range(0, chunk_size):  # 2**(nstages-stage-1)
            twiddles[twiddle_idx + i] = CFixed(
                (
                    sine_wave_in[int((twiddle_idx + SIZE_FFT // 4) % SIZE_FFT)],  # cos
                    sine_wave_in[int((twiddle_idx + SIZE_FFT // 2) % SIZE_FFT)],  # -sin
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
    for i in range(n_stages):
        twiddles = twiddle_generator(bit_width, decimal_pt, n_samples, i)
        new_data = []
        for j in range(int(n_samples // 2)):
            new_data += list(butterfly(data[j * 2], data[j * 2 + 1], twiddles[j]))
        data = stride_permutation(n_samples, new_data)
    return data
