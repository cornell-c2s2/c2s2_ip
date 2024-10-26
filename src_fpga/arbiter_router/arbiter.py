from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 harness for the `Arbiter` module.
class Arbiter(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, nbits, ninputs):
        # Interface
        s.istream = [stream.ifcs.RecvIfcRTL(mk_bits(nbits)) for _ in range(ninputs)]
        s.ostream = stream.ifcs.SendIfcRTL(mk_bits(nbits + (ninputs - 1).bit_length()))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Arbiter")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "arbiter.v"),
        )
