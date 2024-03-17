from pymtl3 import mk_bits, InPort, OutPort, Component
from pymtl3.passes.backends.verilog import VerilogPlaceholder, VerilogPlaceholderPass
from os import path


class ComplexMultiplier(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, p_nbits, p_reset_value):
        # Interface
        s.d = InPort()
        s.en = InPort()

        s.load = InPort(mk_bits(p_nbits))
        s.load_en = InPort()

        s.q = OutPort(mk_bits(p_nbits))

        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "bitwise.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Bitwise")
