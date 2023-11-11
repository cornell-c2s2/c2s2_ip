from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.serdes.deserializer import Deserializer


# Sine Wave Generator
class SineWave(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, N, W, D):
        # Interface

        s.sine_wave_out = [OutPort(W) for _ in range(N)]

        s.set_metadata(VerilogPlaceholderPass.top_module, "SineWave")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "sine_wave.v"),
        )
