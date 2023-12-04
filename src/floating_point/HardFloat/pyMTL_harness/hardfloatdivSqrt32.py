# from tkinter import S
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 wrapper for the Hardfloat multiplier module.
class divSqrtRecFN_small(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, expWidth=8, sigWidth=23, options=0):
        # Interface
        s.control        = InPort (1)
        s.sqrtOp         = InPort (1)
        s.a              = InPort (32)
        s.b              = InPort (32)
        s.roundingMode   = InPort (3)

        s.sqrtOpOut      = OutPort(1)
        s.out            = OutPort(32)
        s.exceptionFlags = OutPort(5)

        s.inReady        = OutPort(1)
        s.inValid        = InPort(1)
        s.outValid       = OutPort(1)
        
        

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "divSqrtRecFN_small")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../source/divSqrtRecFN_small.v"),
        )
