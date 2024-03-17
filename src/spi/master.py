from os import path
from pymtl3 import mk_bits, Component, clog2, InPort, OutPort, Interface
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.stream.ifcs import RecvIfcRTL, SendIfcRTL
from src.spi.interfaces import SPIMasterIfc


class SPIMaster(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, nbits=34, ncs=1):
        # Local parameters
        s.nbits = nbits  # size of message
        s.ncs = ncs  # number of chip select lines
        s.logBitsN = mk_bits(
            clog2(nbits) + 1
        )  # number of bits required to count to packet size

        # Interface
        s.spi_ifc = SPIMasterIfc(ncs)

        s.send = SendIfcRTL(mk_bits(s.nbits))
        s.recv = RecvIfcRTL(mk_bits(s.nbits))

        s.packet_size_ifc = RecvIfcRTL(s.logBitsN)  # size of spi packet (up to nbits)
        s.cs_addr_ifc = RecvIfcRTL(mk_bits(clog2(s.ncs) if s.ncs > 1 else 1))
        s.freq_ifc = RecvIfcRTL(mk_bits(3))

        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "master.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Master")
