from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 harness for the `AMaxbMin` module.
class AMaxbMin(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=16, F_BITS=8):
        # Interface
        s.set_metadata(VerilogTranslationPass.explicit_module_name, "a_maxb_min")

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "AMaxbMin")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../a_maxb_min.v"),
        )
