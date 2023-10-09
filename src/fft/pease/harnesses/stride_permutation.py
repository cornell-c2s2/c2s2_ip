from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


class StridePermutation(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, N_SAMPLES=8, BIT_WIDTH=32):
        # Interface
        s.recv = [InPort(BIT_WIDTH) for _ in range(N_SAMPLES)]
        s.send = [OutPort(BIT_WIDTH) for _ in range(N_SAMPLES)]

        s.set_metadata(VerilogPlaceholderPass.top_module, "StridePermutation")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../helpers/stride_permutation.v"),
        )
