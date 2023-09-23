from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *


# Pymtl3 harness for the `Dds` module.
class Dds(VerilogPlaceholder, Component):
    # Constructor

    def construct(s):
        # Interface

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(n))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(n))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Dds")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(VerilogPlaceholderPass.src_file, "../src/dds/dds.v")
