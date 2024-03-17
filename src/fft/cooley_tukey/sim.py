from fixedpt import CFixed
import math
from src.fixed_point.sim import butterfly
from src.fft.sim import sine_wave, bit_reverse

# Exact simulation of the cooley tukey fft


# Implements the FFT Xbar
def crossbar(
    n_samples: int, stage_fft: int, cbar_in: list[any], front: bool
) -> list[any]:
    cbar_out = [None for _ in range(n_samples)]

    for m in range(2**stage_fft):
        for i in range(m, n_samples, 2 ** (stage_fft + 1)):
            if front:
                cbar_out[i + m] = cbar_in[i]
                cbar_out[i + m + 1] = cbar_in[i + 2**stage_fft]
            else:
                cbar_out[i] = cbar_in[i + m]
                cbar_out[i + 2**stage_fft] = cbar_in[i + m + 1]

    return cbar_out


# Twiddle factor generator
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


# Implements one stage of the FFT
def fft_stage(
    fft_stage_in: list[CFixed],
    stage_fft: int,
    bit_width: int,
    decimal_pt: int,
    n_samples: int,
) -> list[CFixed]:
    buf_in = [None for _ in range(n_samples)]
    buf_out = [None for _ in range(n_samples)]

    buf_in = crossbar(n_samples, stage_fft, fft_stage_in, True)
    # Twiddles
    twiddles = twiddle_generator(bit_width, decimal_pt, n_samples, stage_fft)

    # Butterflies
    for b in range(0, n_samples // 2):
        (buf_out[b * 2], buf_out[b * 2 + 1]) = butterfly(
            buf_in[b * 2], buf_in[b * 2 + 1], twiddles[b]
        )

    # Back crossbar
    output = crossbar(n_samples, stage_fft, buf_out, False)

    return output


# Implements the entire FFT
def fft(
    fft_in: list[CFixed], bit_width: int, decimal_pt: int, n_samples: int
) -> list[CFixed]:
    # Bit reversal
    data = bit_reverse(fft_in, n_samples)

    # FFT Stages
    for i in range(0, math.ceil(math.log2(n_samples))):
        data = fft_stage(data, i, bit_width, decimal_pt, n_samples)

    return data
