from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


class Multiplier(VerilogPlaceholder, Component):
    def construct(s, n, d, sign):
        s.a = InPort(n)
        s.b = InPort(n)
        s.c = OutPort(n)

        s.set_metadata(VerilogPlaceholderPass.top_module, "Multiplier")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "multiplier.v"),
        )
