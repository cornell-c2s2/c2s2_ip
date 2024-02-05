from abc import ABC, abstractmethod
from fixedpt import CFixed
import numpy as np
from src.fixed_point.iterative.tests.fft_sim import fft

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
        # TODO: Implement the exact FFT algorithm
        # Convert the data to a list of complex numbers
        d = [complex(x) for x in data]

        # Perform the FFT
        d = fft(d, self.bit_width, self.decimal_pt, self.n_samples)

        return [CFixed(x, self.bit_width, self.decimal_pt) for x in d]

