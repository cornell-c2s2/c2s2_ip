from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 harness for the `Classifier` module.
class Classifier(VerilogPlaceholder, Component):
    # Constructor

    def construct(BIT_WIDTH=32, DECIMAL_PT = 16, N_SAMPLES = 8):
        # Interface

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH*N_SAMPLES))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(1))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Classifier")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "classifier.v"),
        )
