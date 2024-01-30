from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.fixed_point.utils import mk_butterfly_input, mk_butterfly_output


def mk_multi_butterfly_input(nbits, b):
    @bitstruct
    class MultiButterflyInput:
        list: [mk_butterfly_input(nbits) for _ in range(b)]

    return MultiButterflyInput


def mk_multi_butterfly_output(nbits, b):
    @bitstruct
    class MultiButterflyOutput:
        list: [mk_butterfly_output(nbits) for _ in range(b)]

    return MultiButterflyOutput


class MultiButterfly(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n, d, b):
        # Interface
        s.ar = [InPort(n) for _ in range(b)]
        s.ac = [InPort(n) for _ in range(b)]
        s.br = [InPort(n) for _ in range(b)]
        s.bc = [InPort(n) for _ in range(b)]
        # Omega value
        s.wr = [InPort(n) for _ in range(b)]
        s.wc = [InPort(n) for _ in range(b)]

        s.cr = [OutPort(n) for _ in range(b)]
        s.cc = [OutPort(n) for _ in range(b)]
        s.dr = [OutPort(n) for _ in range(b)]
        s.dc = [OutPort(n) for _ in range(b)]

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


class MultiButterflyWrapper(Component):
    def construct(s, n, d, b):
        s.dut = MultiButterfly(n, d, b)
        s.recv = stream.ifcs.RecvIfcRTL(mk_multi_butterfly_input(n, b))
        for i in range(b):
            s.recv.msg.list[i].ar //= s.dut.ar[i]
            s.recv.msg.list[i].ac //= s.dut.ac[i]
            s.recv.msg.list[i].br //= s.dut.br[i]
            s.recv.msg.list[i].bc //= s.dut.bc[i]
            s.recv.msg.list[i].wr //= s.dut.wr[i]
            s.recv.msg.list[i].wc //= s.dut.wc[i]

        s.recv.val //= s.dut.recv_val
        s.dut.recv_rdy //= s.recv.rdy
        s.send = stream.ifcs.SendIfcRTL(mk_multi_butterfly_output(n, b))
        for i in range(b):
            s.dut.cr[i] //= s.send.msg.list[i].cr
            s.dut.cc[i] //= s.send.msg.list[i].cc
            s.dut.dr[i] //= s.send.msg.list[i].dr
            s.dut.dc[i] //= s.send.msg.list[i].dc

        s.dut.send_val //= s.send.val
        s.send.rdy //= s.dut.send_rdy
