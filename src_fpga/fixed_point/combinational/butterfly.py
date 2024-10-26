from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


class Butterfly(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n, d, b):
        # Interface
        s.ar = [InPort(n) for _ in range(b)]
        s.ac = [InPort(n) for _ in range(b)]
        s.br = [InPort(n) for _ in range(b)]
        s.bc = [InPort(n) for _ in range(b)]
        s.wr = [InPort(n) for _ in range(b)]
        s.wc = [InPort(n) for _ in range(b)]

        s.cr = [OutPort(n) for _ in range(b)]
        s.cc = [OutPort(n) for _ in range(b)]
        s.dr = [OutPort(n) for _ in range(b)]
        s.dc = [OutPort(n) for _ in range(b)]

        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "butterfly.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Butterfly")
