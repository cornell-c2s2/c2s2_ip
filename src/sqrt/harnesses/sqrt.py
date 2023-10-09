# This is the PyMTL wrapper for the corresponding Verilog RTL model sqrt.

from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *


class SqrtTestHarness( VerilogPlaceholder, Component ):

  # Constructor

  def construct( s, BIT_WIDTH = 32):

    s.set_metadata( VerilogTranslationPass.explicit_module_name, 'sqrt' )

    s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
    s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

    # Name of the top level module to be imported
    s.set_metadata(VerilogPlaceholderPass.top_module, "SqrtHarness")
    # Source file path
    s.set_metadata(
        VerilogPlaceholderPass.src_file,
        "../src/sqrt/harnesses/sqrt.v",
    )
