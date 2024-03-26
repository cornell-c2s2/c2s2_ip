from pymtl3 import *
from pymtl3.stdlib.stream.ifcs import RecvIfcRTL, SendIfcRTL
from pymtl3.passes.backends.verilog import *
from os import path
from tools.utils import mk_list_bitstruct
from src.fixed_point.utils import mk_butterfly_input, mk_butterfly_output


class MultiButterfly(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n, d, b):
        # Interface
        s.recv_val = InPort()
        s.recv_rdy = OutPort()

        s.send_val = OutPort()
        s.send_rdy = InPort()

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
            path.join(path.dirname(__file__), "multi_butterfly.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "MultiButterfly")


class MultiButterflyWrapper(Component):
    def construct(s, n, d, b):
        s.dut = MultiButterfly(n, d, b)

        s.recv = RecvIfcRTL(mk_list_bitstruct(mk_butterfly_input(n), b))
        s.send = SendIfcRTL(mk_list_bitstruct(mk_butterfly_output(n), b))

        s.dut.recv_rdy //= s.recv.rdy
        s.recv.val //= s.dut.recv_val

        for i in range(b):
            print(s.recv.msg.list[i]._dsl)
            s.recv.msg.list[i].ar //= s.dut.ar[i]
            s.recv.msg.list[i].ac //= s.dut.ac[i]
            s.recv.msg.list[i].br //= s.dut.br[i]
            s.recv.msg.list[i].bc //= s.dut.bc[i]
            s.recv.msg.list[i].wr //= s.dut.wr[i]
            s.recv.msg.list[i].wc //= s.dut.wc[i]

        s.send.rdy //= s.dut.send_rdy
        s.dut.send_val //= s.send.val

        for i in range(b):
            s.dut.cr[i] //= s.send.msg.list[i].cr
            s.dut.cc[i] //= s.send.msg.list[i].cc
            s.dut.dr[i] //= s.send.msg.list[i].dr
            s.dut.dc[i] //= s.send.msg.list[i].dc
