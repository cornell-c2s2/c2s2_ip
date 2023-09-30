#=========================================================================
# Fixed Point Combinational Multiplier PyMTL3 Wrapper
#=========================================================================

from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path

class FpCombMultVRTL( VerilogPlaceholder, Component ):
  def construct( s, n = 32, d = 16, sign = 1 ):
    s.a       = InPort  ( n )
    s.b       = InPort  ( n )
    s.c       = OutPort ( n )

    s.set_metadata( VerilogPlaceholderPass.top_module, 'FpCombMultVRTL')
    s.set_metadata( VerilogPlaceholderPass.src_file, path.dirname(__file__) + '/../FpCombMultVRTL.v' )