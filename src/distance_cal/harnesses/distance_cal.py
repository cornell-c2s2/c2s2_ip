from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 harness for the `AMaxbMin` module.
class DCalTestHarness(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=32, F_BITS=16):
        # Interface
        s.set_metadata(VerilogTranslationPass.explicit_module_name, "distance_cal")

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(2*BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "HarnessDCal")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            "../src/distance_cal/harnesses/distance_cal.v",
        )
