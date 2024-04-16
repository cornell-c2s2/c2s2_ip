from pymtl3 import *
from pymtl3.stdlib.stream.ifcs import RecvIfcRTL, SendIfcRTL
from pymtl3.passes.backends.verilog import *
from os import path
from tools.utils import mk_list_bitstruct


class CrossbarController(VerilogPlaceholder, Component):
    # Constructor
    def construct(s):
        s.set_metadata(
            VerilogTranslationPass.explicit_module_name, "crossbar_controller"
        )
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "crossbar_controller.v"),
        )
