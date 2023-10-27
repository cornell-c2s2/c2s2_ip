from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 harness for the `CombFloatAdder` module.
class CombFloatAdder(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=32):
        # Interface
        s.a = InPort(32)
        s.b = InPort(32)
        s.out = OutPort(32)

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "CombFloatAdder")

        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "adder.v"),
        )
