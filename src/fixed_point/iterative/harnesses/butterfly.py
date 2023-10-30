from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


def mk_butterfly_input(nbits):
    @bitstruct
    class ButterflyInput:
        ar: mk_bits(nbits)
        ac: mk_bits(nbits)
        br: mk_bits(nbits)
        bc: mk_bits(nbits)
        # Omega value
        wr: mk_bits(nbits)
        wc: mk_bits(nbits)

    return ButterflyInput


def mk_butterfly_output(nbits):
    @bitstruct
    class ButterflyOutput:
        cr: mk_bits(nbits)
        cc: mk_bits(nbits)
        dr: mk_bits(nbits)
        dc: mk_bits(nbits)

    return ButterflyOutput


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
            path.join(path.dirname(__file__), "../butterfly.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(
            VerilogPlaceholderPass.top_module, "FixedPointIterativeButterfly"
        )


class ButterflyHarness(Component):
    def construct(s, n, d, mult):
        s.btfly = Butterfly(n, d, mult)
        s.recv = stream.ifcs.RecvIfcRTL(mk_butterfly_input(n))
        s.recv.msg.ar //= s.btfly.ar
        s.recv.msg.ac //= s.btfly.ac
        s.recv.msg.br //= s.btfly.br
        s.recv.msg.bc //= s.btfly.bc
        s.recv.msg.wr //= s.btfly.wr
        s.recv.msg.wc //= s.btfly.wc

        s.recv.val //= s.btfly.recv_val
        s.btfly.recv_rdy //= s.recv.rdy
        s.send = stream.ifcs.SendIfcRTL(mk_butterfly_output(n))
        s.btfly.cr //= s.send.msg.cr
        s.btfly.cc //= s.send.msg.cc
        s.btfly.dr //= s.send.msg.dr
        s.btfly.dc //= s.send.msg.dc

        s.btfly.send_val //= s.send.val
        s.send.rdy //= s.btfly.send_rdy
