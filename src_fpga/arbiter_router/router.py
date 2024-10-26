from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path
from pymtl3.stdlib import stream


class Router(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, nbits, noutputs):
        s.istream = stream.ifcs.RecvIfcRTL(mk_bits(nbits))
        s.ostream = [stream.ifcs.SendIfcRTL(mk_bits(nbits)) for _ in range(noutputs)]

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Router")
        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "router.v"),
        )
