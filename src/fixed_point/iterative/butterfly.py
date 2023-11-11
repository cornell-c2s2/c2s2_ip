from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.fixed_point.utils import mk_butterfly_input, mk_butterfly_output


class Butterfly(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n, d, mult):
        # Interface
        s.ar = InPort(mk_bits(n))
        s.ac = InPort(mk_bits(n))
        s.br = InPort(mk_bits(n))
        s.bc = InPort(mk_bits(n))
        # Omega value
        s.wr = InPort(mk_bits(n))
        s.wc = InPort(mk_bits(n))

        s.cr = OutPort(mk_bits(n))
        s.cc = OutPort(mk_bits(n))
        s.dr = OutPort(mk_bits(n))
        s.dc = OutPort(mk_bits(n))

        s.recv_val = InPort()
        s.recv_rdy = OutPort()
        s.send_val = OutPort()
        s.send_rdy = InPort()

        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "butterfly.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Butterfly")


class ButterflyWrapper(Component):
    def construct(s, n, d, mult):
        s.dut = Butterfly(n, d, mult)
        s.recv = stream.ifcs.RecvIfcRTL(mk_butterfly_input(n))
        s.recv.msg.ar //= s.dut.ar
        s.recv.msg.ac //= s.dut.ac
        s.recv.msg.br //= s.dut.br
        s.recv.msg.bc //= s.dut.bc
        s.recv.msg.wr //= s.dut.wr
        s.recv.msg.wc //= s.dut.wc

        s.recv.val //= s.dut.recv_val
        s.dut.recv_rdy //= s.recv.rdy
        s.send = stream.ifcs.SendIfcRTL(mk_butterfly_output(n))
        s.dut.cr //= s.send.msg.cr
        s.dut.cc //= s.send.msg.cc
        s.dut.dr //= s.send.msg.dr
        s.dut.dc //= s.send.msg.dc

        s.dut.send_val //= s.send.val
        s.send.rdy //= s.dut.send_rdy
