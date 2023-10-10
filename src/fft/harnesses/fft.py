from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *


# Pymtl3 harness for the `FFT` module.
class FFTTestHarness(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=32, DECIMAL_PT=16, N_SAMPLES=8):
        # Interface

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "FFTHarness")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(VerilogPlaceholderPass.src_file, "../src/fft/harnesses/fft.v")
