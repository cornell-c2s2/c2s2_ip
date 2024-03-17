import math
from fixedpt import Fixed


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
