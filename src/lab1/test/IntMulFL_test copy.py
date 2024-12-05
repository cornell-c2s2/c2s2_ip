#=========================================================================
# IntMulFL_test
#=========================================================================

import pytest

from random import randint

from pymtl3 import *
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from pymtl3.stdlib.stream import StreamSourceFL, StreamSinkFL

from lab1_imul.IntMulFL import IntMulFL

#-------------------------------------------------------------------------
# TestHarness
#-------------------------------------------------------------------------

class TestHarness( Component ):

  def construct( s, imul ):

    # Instantiate models

    s.src  = StreamSourceFL( Bits64 )
    s.sink = StreamSinkFL( Bits32 )
    s.imul = imul

    # Connect

    s.src.ostream  //= s.imul.istream
    s.imul.ostream //= s.sink.istream

  def done( s ):
    return s.src.done() and s.sink.done()

  def line_trace( s ):
    return s.src.line_trace() + " > " + s.imul.line_trace() + " > " + s.sink.line_trace()

#-------------------------------------------------------------------------
# mk_imsg/mk_omsg
#-------------------------------------------------------------------------

# Make input message, truncate ints to ensure they fit in 32 bits.

def mk_imsg( a, b ):
  return concat( Bits32( a, trunc_int=True ), Bits32( b, trunc_int=True ) )

# Make output message, truncate ints to ensure they fit in 32 bits.

def mk_omsg( a ):
  return Bits32( a, trunc_int=True )

#----------------------------------------------------------------------
# Test Case: small positive * positive
#----------------------------------------------------------------------

small_pos_pos_msgs = [
  mk_imsg(  2,  3 ), mk_omsg(   6 ),
  mk_imsg(  4,  5 ), mk_omsg(  20 ),
  mk_imsg(  3,  4 ), mk_omsg(  12 ),
  mk_imsg( 10, 13 ), mk_omsg( 130 ),
  mk_imsg(  8,  7 ), mk_omsg(  56 ),
]

large_pos_pos_msgs = [
  mk_imsg( 1419121677, 1039059964), mk_omsg( 45616076),
  mk_imsg( 2293619238, 2697142385), mk_omsg( 4269542086),
  mk_imsg( 1334187506, 3593878096), mk_omsg( 669757344),
  mk_imsg( 637596253, 88787367), mk_omsg( 1758142379),
  mk_imsg( 1787423072, 2879156127), mk_omsg( 1314427552),
  mk_imsg( 4081078878, 3746584479), mk_omsg( 2421234274),
  mk_imsg( 3194088153, 4067270364), mk_omsg( 729596028),
  mk_imsg( 2883203259, 4283513900), mk_omsg( 1561801764),
  mk_imsg( 124043556, 3082472535), mk_omsg( 3712897852),
  mk_imsg( 2975531158, 1358052598), mk_omsg( 794933284),
  mk_imsg( 1203514210, 3910998304), mk_omsg( 1943797312),
  mk_imsg( 2906907885, 1042283831), mk_omsg( 1904699371),
  mk_imsg( 1670750671, 4187785664), mk_omsg( 3035963968),
  mk_imsg( 525840799, 2073179624), mk_omsg( 1089266456),
  mk_imsg( 1604528862, 3478457418), mk_omsg( 149081132),
  mk_imsg( 684054703, 2311867409), mk_omsg( 3286980511),
  mk_imsg( 3564963739, 4179308151), mk_omsg( 3453313805),
  mk_imsg( 2060446933, 306443914), mk_omsg( 4150876370),
  mk_imsg( 1433233799, 3264700263), mk_omsg( 2244972113),
  mk_imsg( 4111003670, 701598399), mk_omsg( 722271338),
  mk_imsg( 2079070988, 4293743394), mk_omsg( 3963800),
  mk_imsg( 777025144, 481707053), mk_omsg( 3706499864),
  mk_imsg( 2525763425, 3566012001), mk_omsg( 2282627521),
  mk_imsg( 3911692374, 1017621681), mk_omsg( 251966326),
  mk_imsg( 3422146826, 938093632), mk_omsg( 663091840),
  mk_imsg( 2426716779, 143725066), mk_omsg( 2998279726),
  mk_imsg( 1246858492, 3923019637), mk_omsg( 357454636),
  mk_imsg( 257485965, 3288084285), mk_omsg( 1030373529),
  mk_imsg( 3027114333, 2998704365), mk_omsg( 3007886105),
  mk_imsg( 1627819059, 1082230528), mk_omsg( 3651265792),
]

small_neg_neg_msgs = [
  mk_imsg( -137, -106), mk_omsg( 14522),
  mk_imsg( -127, -85), mk_omsg( 10795),
  mk_imsg( -246, -111), mk_omsg( 27306),
  mk_imsg( -34, -108), mk_omsg( 3672),
  mk_imsg( -172, -125), mk_omsg( 21500),
  mk_imsg( -216, -154), mk_omsg( 33264),
  mk_imsg( -54, -21), mk_omsg( 1134),
  mk_imsg( -198, -191), mk_omsg( 37818),
  mk_imsg( -18, -19), mk_omsg( 342),
  mk_imsg( -99, -49), mk_omsg( 4851),
  mk_imsg( -148, -35), mk_omsg( 5180),
  mk_imsg( -55, -1), mk_omsg( 55),
  mk_imsg( -225, -137), mk_omsg( 30825),
  mk_imsg( -197, -190), mk_omsg( 37430),
  mk_imsg( -58, -243), mk_omsg( 14094),
  mk_imsg( -46, -161), mk_omsg( 7406),
  mk_imsg( -139, -197), mk_omsg( 27383),
  mk_imsg( -240, -34), mk_omsg( 8160),
  mk_imsg( -52, -21), mk_omsg( 1092),
  mk_imsg( -13, -31), mk_omsg( 403),
  mk_imsg( -181, -87), mk_omsg( 15747),
  mk_imsg( -59, -71), mk_omsg( 4189),
  mk_imsg( -37, -62), mk_omsg( 2294),
  mk_imsg( -233, -75), mk_omsg( 17475),
  mk_imsg( -127, -32), mk_omsg( 4064),
  mk_imsg( -195, -106), mk_omsg( 20670),
  mk_imsg( -246, -124), mk_omsg( 30504),
  mk_imsg( -56, -41), mk_omsg( 2296),
  mk_imsg( -183, -44), mk_omsg( 8052),
  mk_imsg( -185, -53), mk_omsg( 9805),
]


#-------------------------------------------------------------------------
# Test Case Table
#-------------------------------------------------------------------------

test_case_table = mk_test_case_table([
  (                      "msgs                   src_delay sink_delay"),
  [ "small_pos_pos",     small_pos_pos_msgs,     0,        0          ],
  [ "large_pos_pos",     large_pos_pos_msgs,     0,        0          ],
  [ "small_neg_neg",     small_pos_pos_msgs,     0,        0          ],


])

#-------------------------------------------------------------------------
# TestHarness
#-------------------------------------------------------------------------

@pytest.mark.parametrize( **test_case_table )
def test( test_params, cmdline_opts ):

  th = TestHarness( IntMulFL() )

  th.set_param("top.src.construct",
    msgs=test_params.msgs[::2],
    initial_delay=test_params.src_delay+3,
    interval_delay=test_params.src_delay )

  th.set_param("top.sink.construct",
    msgs=test_params.msgs[1::2],
    initial_delay=test_params.sink_delay+3,
    interval_delay=test_params.sink_delay )

  run_sim( th, cmdline_opts, duts=['imul'] )

