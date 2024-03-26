from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.fixed_point.utils import (
    mk_complex_multiplier_input,
    mk_complex_multiplier_output,
)


class ComplexMultiplier(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n, d, num_mults=3):
        # Interface
        s.ar = InPort(mk_bits(n))
        s.ac = InPort(mk_bits(n))
        s.br = InPort(mk_bits(n))
        s.bc = InPort(mk_bits(n))

        s.cr = OutPort(mk_bits(n))
        s.cc = OutPort(mk_bits(n))

        s.recv_val = InPort()
        s.recv_rdy = OutPort()
        s.send_val = OutPort()
        s.send_rdy = InPort()

        s.set_metadata(VerilogPlaceholderPass.top_module, "ComplexMultiplier")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "complex_multiplier.v"),
        )


class ComplexMultiplierWrapper(Component):
    def construct(s, n, d, num_mults=3):
        s.dut = ComplexMultiplier(n, d, num_mults)
        s.recv = stream.ifcs.RecvIfcRTL(mk_complex_multiplier_input(n))
        s.recv.msg.ar //= s.dut.ar
        s.recv.msg.ac //= s.dut.ac
        s.recv.msg.br //= s.dut.br
        s.recv.msg.bc //= s.dut.bc

        s.recv.val //= s.dut.recv_val
        s.dut.recv_rdy //= s.recv.rdy
        s.send = stream.ifcs.SendIfcRTL(mk_complex_multiplier_output(n))
        s.dut.cr //= s.send.msg.cr
        s.dut.cc //= s.send.msg.cc

        s.dut.send_val //= s.send.val
        s.send.rdy //= s.dut.send_rdy

    def line_trace(s):
        return s.dut.line_trace()
