from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from tools.utils import mk_list_bitstruct


class CrossbarController(VerilogPlaceholder, Component):
    # Constructor
    def construct(s):
        s.indata = InPort(6)
        s.w = InPort(1)
        s.s = InPort(1)
        s.defaultout = OutPort(6)

        s.set_metadata(
            VerilogTranslationPass.explicit_module_name, "crossbar_controller"
        )
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "crossbar_controller.v"),
        )
