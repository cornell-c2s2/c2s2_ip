from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 harness for the `LbistController` module.
class LbistController(VerilogPlaceholder, Component):
    # Constructor

    def construct(s):
        # Interface

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(n))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(n))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "LbistController")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "lbist_controller.v"),
        )
