from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


class MultiplierTestHarness(VerilogPlaceholder, Component):
    def construct(s, n=32, d=16, sign=1):
        s.a = InPort(n)
        s.b = InPort(n)
        s.c = OutPort(n)

        s.set_metadata(VerilogPlaceholderPass.top_module, "FixedPointCombMultiplier")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../multiplier.v"),
        )
