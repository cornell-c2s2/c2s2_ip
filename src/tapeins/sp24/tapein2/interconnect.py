from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


class Interconnect(VerilogPlaceholder, Component):
    # Constructor

    def construct(s):
        s.cs = InPort(1)
        s.mosi = InPort(1)
        s.miso = OutPort(1)
        s.sclk = InPort(1)
        s.minion_parity = OutPort(1)
        s.adapter_parity = OutPort(1)

        s.input_xbar_input_override = InPort(1)
        s.input_xbar_output_override = InPort(1)
        s.classifier_xbar_input_override = InPort(1)
        s.classifier_xbar_output_override = InPort(1)
        s.output_xbar_input_override = InPort(1)
        s.output_xbar_output_override = InPort(1)

        s.wbs_stb_i = InPort(1)
        s.wbs_cyc_i = InPort(1)
        s.wbs_we_i = InPort(1)
        s.wbs_sel_i = InPort(4)
        s.wbs_dat_i = InPort(32)
        s.wbs_adr_i = InPort(32)
        s.wbs_ack_o = OutPort(1)
        s.wbs_dat_o = OutPort(32)

        # unused ports
        s.io_oeb = OutPort(23)
        s.io_out = OutPort(5)

        s.set_metadata(VerilogPlaceholderPass.top_module, "Interconnect")

        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "interconnect.v"),
        )
