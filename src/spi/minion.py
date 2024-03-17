from os import path
from pymtl3 import mk_bits, Component, clog2, InPort, OutPort, Interface
from pymtl3.passes.backends.verilog import VerilogPlaceholder, VerilogPlaceholderPass
from pymtl3.stdlib.stream.ifcs import RecvIfcRTL, SendIfcRTL
from src.spi.interfaces import SPIMinionIfc, PushOutIfc, PullInIfc


class SPIMinion(VerilogPlaceholder, Component):

    # Constructor

    def construct(s, nbits=8):
        s.spi_min = SPIMinionIfc()
        s.push = PushOutIfc(nbits)
        s.pull = PullInIfc(nbits)
        s.parity = OutPort()

        s.set_metadata(
            VerilogPlaceholderPass.port_map,
            {
                s.spi_min.cs: "cs",
                s.spi_min.sclk: "sclk",
                s.spi_min.mosi: "mosi",
                s.spi_min.miso: "miso",
                s.push.en: "push_en",
                s.push.msg: "push_msg",
                s.pull.en: "pull_en",
                s.pull.msg: "pull_msg",
                s.parity: "parity",
            },
        )

        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "minion.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Minion")
