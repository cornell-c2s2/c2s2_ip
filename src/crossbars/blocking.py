# This is the PyMTL wrapper for the corresponding Verilog RTL model CrossbarVRTL.

from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path

class Blocking(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH: int, N_INPUTS: int, N_OUTPUTS: int, CONTROL_BIT_WIDTH: int):
        # Interface
        s.recv = [stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH)) for _ in range(N_INPUTS)]
        s.control = stream.ifcs.RecvIfcRTL(mk_bits(CONTROL_BIT_WIDTH))
        s.send = [stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH)) for _ in range(N_OUTPUTS)]

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Blocking")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "blocking.v"),
        )
