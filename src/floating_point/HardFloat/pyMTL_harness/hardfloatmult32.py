from tkinter import S
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 wrapper for the Hardfloat multiplier module.
class mulRecFN(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, expWidth=8, sigWidth=23):
        # Interface
        s.control        = InPort (1)
        s.a              = InPort (32)
        s.b              = InPort (32)
        s.roundingMode   = InPort (3)
        s.out            = OutPort(32)
        s.exceptionFlags = OutPort(5)

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "mulRecFN")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../source/mulRecFN.v"),
        )
