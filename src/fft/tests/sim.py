from abc import ABC, abstractmethod
from fixedpt import CFixed
from fixedpt import Fixed
import numpy as np
import math
from src.fixed_point.iterative.tests.butterfly import butterfly
from src.fft.tests.sine_wave import sine_wave
from src.fft.tests.twiddle_generator import twiddle_generator
from src.fft.tests.crossbar import crossbar


# Python interface for the FFT module
class FFTInterface(ABC):
    def __init__(self, bit_width, decimal_pt, n_samples):
        self.bit_width = bit_width
        self.decimal_pt = decimal_pt
        self.n_samples = n_samples

    @abstractmethod
    def transform(self, data: list[CFixed]) -> list[CFixed]:
        # Perform the FFT on the given data
        pass


# Version of the FFT simulation that uses a normal numpy FFT algorithm. This is used to verify the Verilog implementation approximately.
class FFTNumpy(FFTInterface):
    def transform(self, data: list[CFixed]) -> list[CFixed]:
        # Convert the data to a list of complex numbers
        d = [complex(x) for x in data]

        # Perform the FFT
        d = np.fft.fft(d, self.n_samples)

        return [CFixed(x, self.bit_width, self.decimal_pt) for x in d]


# Version of the FFT simulation that uses the exact same algorithm as the Verilog implementation. This is used to verify the Verilog implementation.
class FFTExact(FFTInterface):
    def transform(self, data: list[CFixed]) -> list[CFixed]:

        # Implements bit reverse
        def bit_reverse(rev_in: list, n_samples: int):
            out = [0] * n_samples

            n = math.ceil(math.log2(n_samples))

            for m in range(0, n_samples):
                m_rev = format(m, f"0{n}b")[::-1]
                reversed_index = int(m_rev, 2)
                out[reversed_index] = rev_in[m]

            return out

        # Implements one stage of the FFT
        def fft_stage(
            fft_stage_in: list[CFixed],
            sine_wave_in: list[Fixed],
            stage_fft=0,
            bit_width=32,
            decimal_pt=16,
            n_samples=8,
        ):
            buf_in = [None for _ in range(n_samples)]
            buf_out = [None for _ in range(n_samples)]

            buf_in = crossbar(n_samples, stage_fft, fft_stage_in, True)
            # Twiddles
            twiddles = twiddle_generator(bit_width, decimal_pt, n_samples, stage_fft)

            # Butterflies
            for b in range(0, n_samples // 2):
                (buf_out[b * 2], buf_out[b * 2 + 1]) = butterfly(
                    bit_width, decimal_pt, buf_in[b * 2], buf_in[b * 2 + 1],  twiddles[b]
                )

            # Back crossbar
            output = crossbar(n_samples, stage_fft, buf_out, False)

            return output

        # Implements fft
        def fft(fft_in: list[CFixed], bit_width=32, decimal_pt=16, n_samples=8):
            data = fft_in

            # Bit reverse
            data = bit_reverse(data, n_samples)  # Do bit reversal

            # get sine wave
            sine_wave_in = sine_wave(n_samples, bit_width, decimal_pt)

            # FFT Stages
            for i in range(0, math.ceil(math.log2(n_samples))):
                data = fft_stage(
                    data, sine_wave_in, i, bit_width, decimal_pt, n_samples
                )

            return data

        return fft(data, self.bit_width, self.decimal_pt, self.n_samples)
