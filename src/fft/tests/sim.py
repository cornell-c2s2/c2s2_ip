from abc import ABC, abstractmethod
from fixedpt import CFixed
from fixedpt import Fixed
import numpy as np
import math
from src.fixed_point.iterative.tests.butterfly import butterfly


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
        def sine_wave(n_samples, bit_width, decimal_pt) -> list[Fixed]:
            fixed_sinvalue = [Fixed(0, 1, bit_width, decimal_pt)] * n_samples
            for i in range(n_samples):
                sinvalue = np.sin(2 * np.pi * i / n_samples)
                fixed_sinvalue[i] = Fixed(sinvalue, 1, bit_width, decimal_pt)
            return fixed_sinvalue

        # Implements twiddle generator
        def twiddle_gen(
            sine_wave_in: list[Fixed],
            bit_width=4,
            decimal_pt=2,
            size_fft=8,
            stage_fft=0,
        ) -> list[CFixed]:
            twiddles = [0] * (size_fft // 2)

            for m in range(0, 2**stage_fft):
                for i in range(0, size_fft, 2 ** (stage_fft + 1)):
                    idx = m * size_fft / (1 << (stage_fft + 1))
                    twiddles[(i // 2) + m] = CFixed(
                        (
                            sine_wave_in[int((idx + size_fft / 4) % size_fft)],
                            -sine_wave_in[int(idx % size_fft)],
                        ),
                        bit_width,
                        decimal_pt,
                    )

            return twiddles

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
            buf_in = [0] * n_samples
            buf_out = [0] * n_samples

            # Front crossbar
            for m in range(0, 2**stage_fft):
                for i in range(m, n_samples, 2 ** (stage_fft + 1)):
                    buf_in[i + m] = fft_stage_in[i]
                    buf_in[i + m + 1] = fft_stage_in[i + 2**stage_fft]

            # Twiddles
            twiddles = twiddle_gen(
                sine_wave_in, bit_width, decimal_pt, n_samples, stage_fft
            )

            # Butterflies
            for b in range(0, n_samples // 2):
                (buf_out[b * 2], buf_out[b * 2 + 1]) = butterfly(
                    bit_width, decimal_pt, twiddles[b], buf_in[b * 2], buf_in[b * 2 + 1]
                )

            output = [0] * n_samples

            # Back crossbar
            for m in range(0, 2**stage_fft):
                for i in range(m, n_samples, 2 ** (stage_fft + 1)):
                    output[i] = buf_out[i + m]
                    output[i + 2**stage_fft] = buf_out[i + m + 1]

            return output

        # Implements fft
        def fft(fft_in: list[CFixed], bit_width=32, decimal_pt=16, n_samples=8):
            # msg = [
            #     [CFixed((0, 0), bit_width, decimal_pt) for _ in range(n_samples)]
            #     for _ in range(math.ceil(math.log2(n_samples) + 1))
            # ]

            # # Bit reverse
            # msg[0] = bit_reverse(fft_in, n_samples)

            # # FFT Stages
            # for i in range(0, math.ceil(math.log2(n_samples))):
            #     msg[i + 1] = fft_stage(msg[i], i, bit_width, decimal_pt, n_samples)

            # # FFT Out
            # fft_out = [0] * n_samples
            # for i in range(0, n_samples):
            #     fft_out[i] = msg[math.ceil(math.log2(n_samples))][i]

            # return fft_out
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
