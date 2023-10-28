from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


class Crossbar(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=1, SIZE_FFT=2, STAGE_FFT=0, FRONT=1):
        # Interface
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(2 * BIT_WIDTH * SIZE_FFT))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(2 * BIT_WIDTH * SIZE_FFT))

        s.set_metadata(VerilogPlaceholderPass.top_module, "CrossbarTestHarness")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "crossbar.v"),
        )
