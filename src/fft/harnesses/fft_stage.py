from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *


class FFTStageTestHarness(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=32, DECIMAL_PT=16, N_SAMPLES=8, STAGE_FFT=0):
        # Interface
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        s.set_metadata(VerilogPlaceholderPass.top_module, "FFTStageHarness")
        s.set_metadata(
            VerilogPlaceholderPass.src_file, "../src/fft/harnesses/fft_stage.v"
        )
