# This is the PyMTL wrapper for the corresponding Verilog RTL model fxp_sqrt.

from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


class FxpSqrtTestHarness(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=16, F_BITS=8):
        s.set_metadata(VerilogTranslationPass.explicit_module_name, "fxp_sqrt")

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Fxp_sqrt")
        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../fxp_sqrt.v"),
        )
