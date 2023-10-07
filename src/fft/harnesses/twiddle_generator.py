from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


class TwiddleGenerator(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=4, DECIMAL_PT=1, SIZE_FFT=8, STAGE_FFT=0):
        # Interface
        s.send_msg = OutPort(BIT_WIDTH * SIZE_FFT)

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "TwiddleGeneratorHarness")
        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "twiddle_generator.v"),
        )
