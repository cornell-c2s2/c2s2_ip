from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 wrapper for the `CombFloatSubtractor` module.
class CombFloatAdderWrapper(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, BIT_WIDTH=32, M_WIDTH=23, E_WIDTH=8):
        # Interface
        s.in0 = InPort(BIT_WIDTH)
        s.in1 = InPort(BIT_WIDTH)
        s.out = OutPort(BIT_WIDTH)

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "FloatCombAdder")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../adder.v"),
        )
