from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


# Sine Wave Generator
class TwiddleGenerator(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH, DECIMAL_PT, SIZE_FFT, STAGE_FFT):
        # Interface

        s.sine_wave_in = [InPort(BIT_WIDTH) for _ in range(SIZE_FFT)]

        s.twiddle_real = [OutPort(BIT_WIDTH) for _ in range(SIZE_FFT // 2)]
        s.twiddle_imaginary = [OutPort(BIT_WIDTH) for _ in range(SIZE_FFT // 2)]

        s.set_metadata(VerilogPlaceholderPass.top_module, "TwiddleGenerator")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "twiddle_generator.v"),
        )
