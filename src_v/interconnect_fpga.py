from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path

class Interconnect_Fpga(VerilogPlaceholder, Component):
    # Constructor

    def construct(s):
        s.cs = InPort(1)
        s.mosi = InPort(1)
        s.miso = OutPort(1)
        s.sclk = InPort(1)
        s.minion_parity = OutPort(1)
        s.adapter_parity = OutPort(1)

        s.set_metadata(VerilogPlaceholderPass.top_module, "interconnect_fpga_top")

        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "interconnect_fpga.v"),
        )