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

    def construct(s, n=32, d=16, mult=1):
        # Interface
        s.recv = stream.ifcs.RecvIfcRTL(mk_butterfly_input(n))
        s.send = stream.ifcs.SendIfcRTL(mk_butterfly_output(n))

        s.set_metadata(
            VerilogPlaceholderPass.port_map,
            {
                s.recv.msg.ar: "ar",
                s.recv.msg.ac: "ac",
                s.recv.msg.br: "br",
                s.recv.msg.bc: "bc",
                s.recv.msg.wr: "wr",
                s.recv.msg.wc: "wc",
                # Map Outputs
                s.send.msg.cr: "cr",
                s.send.msg.cc: "cc",
                s.send.msg.dr: "dr",
                s.send.msg.dc: "dc",
            },
        )

        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "../butterfly.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(
            VerilogPlaceholderPass.top_module, "FixedPointIterativeButterfly"
        )
