from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *


class DeserializerTestHarnessVRTL(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, BIT_WIDTH=32, N_SAMPLES=8):
        # Interface
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH * N_SAMPLES))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "DeserializerHarness")
        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            "../src/serdes/harnesses/deserializer.v",
        )
