from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *


# Pymtl3 harness for the `CombFloatMultiplier` module.
class CombFloatMultiplier(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH = 32):
        # Interface

        s.in0 = InPort(32)
        s.in1 = InPort(32)
        s.out = OutPort(32)
        
        # s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        # s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "CombFloatMultipler")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(VerilogPlaceholderPass.src_file, "../src/floating_point/comb_floating_point/comb_float_multiplier.v")
