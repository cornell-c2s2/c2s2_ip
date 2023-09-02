from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *

# Pymtl3 harness for the `Template` module.
class Template( VerilogPlaceholder, Component ):
  # Constructor

  def construct( s ):
    # Interface

    s.recv = stream.ifcs.RecvIfcRTL( mk_bits(n) )
    s.send = stream.ifcs.SendIfcRTL( mk_bits(n) )

    # Name of the top level module to be imported
    s.set_metadata( VerilogPlaceholderPass.top_module, 'Template' )
    # Source file path
    s.set_metadata( VerilogPlaceholderPass.src_file, 'template/template.v' )