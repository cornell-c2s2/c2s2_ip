from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *


class HarnessVRTL(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n=32, d=16):
        # Interface

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(4 * n))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(2 * n))

        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            "../src/fixed_point/iterative/harnesses/complex_multiplier.v",
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "HarnessFPICM")
