from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


class HarnessVRTL(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n=32, d=16, b=4):
        # Interface
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(6 * n * b))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(4 * n * b))

        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "butterfly.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "HarnessFXPMB")


class HarnessVRTLWrapper(Component):
    def construct(s, n=32, d=16, b=4):
        s.dut = HarnessVRTL(n, d, b)
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(6 * n * b))
        s.recv //= s.dut.recv
        s.send = stream.ifcs.SendIfcRTL(mk_bits(4 * n * b))
        s.send //= s.dut.send
