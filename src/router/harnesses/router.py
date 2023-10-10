from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


class Router(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, nbits, noutputs):
        s.istream_val = InPort(1)
        s.istream_msg = InPort(mk_bits(nbits))
        s.istream_rdy = OutPort(1)

        s.ostream_val = [OutPort(mk_bits(1)) for _ in range(noutputs)]
        s.ostream_msg = [OutPort(mk_bits(nbits)) for _ in range(noutputs)]
        s.ostream_rdy = [InPort(mk_bits(1)) for _ in range(noutputs)]

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Router")
        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../router.v"),
        )
