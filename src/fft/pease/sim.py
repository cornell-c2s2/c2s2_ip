from fixedpt import CFixed, Fixed
import math

# Implements bit reverse
def bit_reverse(rev_in: list, n_samples: int):
    out = [0] * n_samples

    n = math.ceil(math.log2(n_samples))

    for m in range(0, n_samples):
        m_rev = format(m, f"0{n}b")[::-1]
        reversed_index = int(m_rev, 2)
        out[reversed_index] = rev_in[m]

    return out


# Sine wave generator for the twiddle factors
def sine_wave(n_samples: int, bit_width: int, decimal_pt: int) -> list[Fixed]:
    return [
        Fixed(
            round((math.sin(2 * math.pi * i / n_samples)) * (1 << decimal_pt)),
            1,
            bit_width,
            decimal_pt,
            True,
        )
        for i in range(n_samples)
    ]

# Performs the butterfly operation on two complex numbers
# Used to generate the expected output
def butterfly(a: CFixed, b: CFixed, w: CFixed) -> tuple[CFixed, CFixed]:
    assert a.real._n == b.real._n
    assert a.real._d == b.real._d
    assert a.real._n == w.real._n
    assert a.real._d == w.real._d

    n = a.real._n
    d = a.real._d

    # t = complex_multiply(b, w)
    # t = b.__mul__(w)
    arXbr = w.real.__mul__(b.real).resize(True, n, d)
    acXbc = w.imag.__mul__(b.imag).resize(True, n, d)
    arcXbrc = (w.real + w.imag).resize(True, n, d).__mul__((b.real + b.imag).resize(True, n, d)).resize(True, n, d)
    t = CFixed(((arXbr - acXbc).resize(True, n, d).get(True), (arcXbrc - arXbr - acXbc).resize(True, n, d).get(True)), n, d, True)
    
    # debugging for rounding error
    # print(f"M_CR : {hex(t.real.get(True))}, M_CC : {hex(t.imag.get(True))}")
    # print(f"arXbr : {hex(arXbr.get(True))}")
    # print(f"acXbc : {hex(acXbc.get(True))}")
    # print(f"arXbrc : {hex(arXbrc.get(True))}")
    # print(f"cr : {hex((arXbr - acXbc).get(True))}")
    # print(f"cc : {hex((arXbrc - arXbr - acXbc).get(True))}")
    # print(f"M_CR : {hex(t_new.real.get(True))}, M_CC : {hex(t_new.imag.get(True))}")
    # t = t_new

    return ((a + t).resize(n, d), (a - t).resize(n, d))


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
            # debugging for rounding error
            # print(f"AR : {hex(data[j*2].real.get(True))}, AC: {hex(data[j*2].imag.get(True))}")
            # print(f"BR : {hex(data[j*2+1].real.get(True))}, BC: {hex(data[j*2+1].imag.get(True))}")
            # print(f"WR : {hex(twiddles[j].real.get(True))}, WC: {hex(twiddles[j].imag.get(True))}")

            new_data += list(butterfly(data[j * 2], data[j * 2 + 1], twiddles[j]))

            # print(f"CR : {hex(new_data[-2].real.get(True))}, CC: {hex(new_data[-2].imag.get(True))}")
            # print(f"DR : {hex(new_data[-1].real.get(True))}, DC: {hex(new_data[-1].imag.get(True))}")
            # print()
        data = stride_permutation(n_samples, new_data)
    return data