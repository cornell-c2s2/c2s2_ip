import math
from fixedpt import Fixed


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
