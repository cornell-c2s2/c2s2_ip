from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *

class TemplateVRTL( VerilogPlaceholder, Component ):
  # Constructor

  def construct( s ):
    # Interface

    s.recv = stream.ifcs.RecvIfcRTL( mk_bits(n) )
    s.send = stream.ifcs.SendIfcRTL( mk_bits(n) )