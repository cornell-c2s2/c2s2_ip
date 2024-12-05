#=========================================================================
# Integer Multiplier FL Model
#=========================================================================

from pymtl3 import *
from pymtl3.stdlib.stream.ifcs import IStreamIfc, OStreamIfc
from pymtl3.stdlib.stream      import IStreamDeqAdapterFL, OStreamEnqAdapterFL

class IntMulFL( Component ):

  # Constructor

  def construct( s ):

    # Interface

    s.istream = IStreamIfc( Bits64 )
    s.ostream = OStreamIfc( Bits32 )

    # Queue Adapters

    s.istream_q = IStreamDeqAdapterFL( Bits64 )
    s.ostream_q = OStreamEnqAdapterFL( Bits32 )

    s.istream //= s.istream_q.istream
    s.ostream //= s.ostream_q.ostream

    # FL block

    @update_once
    def block():
      if s.istream_q.deq.rdy() and s.ostream_q.enq.rdy():
        msg = s.istream_q.deq()
        s.ostream_q.enq( msg[32:64] * msg[0:32] )

  # Line tracing

  def line_trace( s ):
    return f"{s.istream}(){s.ostream}"

