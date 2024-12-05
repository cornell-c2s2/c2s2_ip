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

#----------------------------------------------------------------------
# Test Case: zero,one,negative one
#----------------------------------------------------------------------

zero_one_negone_msgs = [
  mk_imsg(  0,  1 ), mk_omsg(   0 ),
  mk_imsg(  1,  1 ), mk_omsg(  1 ),
  mk_imsg(  0,  0 ), mk_omsg(  0 ),
  mk_imsg( -1, 1 ), mk_omsg( -1 ),
  mk_imsg(  0,  -1 ), mk_omsg(  0 ),
]

small_neg_pos_msgs = [
  mk_imsg( -3,  2 ), mk_omsg(  -6 ),
  mk_imsg( -1,  5 ), mk_omsg(  -5 ),
  mk_imsg( -7,  3 ), mk_omsg( -21 ),
  mk_imsg( -2,  4 ), mk_omsg(  -8 ),
  mk_imsg( -6,  2 ), mk_omsg( -12 ),
]

small_pos_neg_msgs = [
  mk_imsg(  2, -3 ), mk_omsg(  -6 ),
  mk_imsg(  5, -1 ), mk_omsg(  -5 ),
  mk_imsg(  3, -7 ), mk_omsg( -21 ),
  mk_imsg(  4, -2 ), mk_omsg(  -8 ),
  mk_imsg(  2, -6 ), mk_omsg( -12 ),
]

small_neg_neg_msgs = [
  mk_imsg( -3, -2 ), mk_omsg(   6 ),
  mk_imsg( -1, -5 ), mk_omsg(   5 ),
  mk_imsg( -7, -3 ), mk_omsg(  21 ),
  mk_imsg( -2, -4 ), mk_omsg(   8 ),
  mk_imsg( -6, -2 ), mk_omsg(  12 ),
]

large_pos_pos_msgs = [
  mk_imsg(      20000,     100000 ), mk_omsg( 2000000000 ),
  mk_imsg(      30000,      50000 ), mk_omsg( 1500000000 ),
  mk_imsg(      40000,      50000 ), mk_omsg( 2000000000 ),
  mk_imsg(      50000,      30000 ), mk_omsg( 1500000000 ),
  mk_imsg(      10000,     200000 ), mk_omsg( 2000000000 ),
  mk_imsg( 1419121677, 1039059964 ), mk_omsg(   45616076 ),
  mk_imsg( 2293619238, 2697142385 ), mk_omsg( 4269542086 ),
  mk_imsg( 1334187506, 3593878096 ), mk_omsg(  669757344 ),
  mk_imsg(  637596253,   88787367 ), mk_omsg( 1758142379 ),
  mk_imsg( 1787423072, 2879156127 ), mk_omsg( 1314427552 ),
  mk_imsg( 4081078878, 3746584479 ), mk_omsg( 2421234274 ),
  mk_imsg( 3194088153, 4067270364 ), mk_omsg(  729596028 ),
  mk_imsg( 2883203259, 4283513900 ), mk_omsg( 1561801764 ),
  mk_imsg(  124043556, 3082472535 ), mk_omsg( 3712897852 ),
  mk_imsg( 2975531158, 1358052598 ), mk_omsg(  794933284 ),
  mk_imsg( 1203514210, 3910998304 ), mk_omsg( 1943797312 ),
  mk_imsg( 2906907885, 1042283831 ), mk_omsg( 1904699371 ),
  mk_imsg( 1670750671, 4187785664 ), mk_omsg( 3035963968 ),
  mk_imsg(  525840799, 2073179624 ), mk_omsg( 1089266456 ),
  mk_imsg( 1604528862, 3478457418 ), mk_omsg(  149081132 ),
  mk_imsg(  684054703, 2311867409 ), mk_omsg( 3286980511 ),
  mk_imsg( 3564963739, 4179308151 ), mk_omsg( 3453313805 ),
  mk_imsg( 2060446933, 306443914  ), mk_omsg( 4150876370 ),
  mk_imsg( 1433233799, 3264700263 ), mk_omsg( 2244972113 ),
  mk_imsg( 4111003670,  701598399 ), mk_omsg(  722271338 ),
  mk_imsg( 2079070988, 4293743394 ), mk_omsg(    3963800 ),
  mk_imsg(  777025144,  481707053 ), mk_omsg( 3706499864 ),
  mk_imsg( 2525763425, 3566012001 ), mk_omsg( 2282627521 ),
  mk_imsg( 3911692374, 1017621681 ), mk_omsg(  251966326 ),
  mk_imsg( 3422146826,  938093632 ), mk_omsg(  663091840 ),
  mk_imsg( 2426716779,  143725066 ), mk_omsg( 2998279726 ),
  mk_imsg( 1246858492, 3923019637 ), mk_omsg(  357454636 ),
  mk_imsg(  257485965, 3288084285 ), mk_omsg( 1030373529 ),
  mk_imsg( 3027114333, 2998704365 ), mk_omsg( 3007886105 ),
  mk_imsg( 1627819059, 1082230528 ), mk_omsg( 3651265792 ),
]

large_pos_neg_msgs = [
  mk_imsg(  20000,  -100000 ), mk_omsg(  -2000000000 ),
  mk_imsg(  30000,  -50000  ), mk_omsg(  -1500000000 ),
  mk_imsg(  40000,  -50000  ), mk_omsg(  -2000000000 ),
  mk_imsg(  50000,  -30000  ), mk_omsg(  -1500000000 ),
  mk_imsg(  10000,  -200000 ), mk_omsg(  -2000000000 ),
]

large_neg_pos_msgs = [
  mk_imsg( -20000,  100000  ), mk_omsg(  -2000000000 ),
  mk_imsg( -30000,  50000   ), mk_omsg(  -1500000000 ),
  mk_imsg( -40000,  50000   ), mk_omsg(  -2000000000 ),
  mk_imsg( -50000,  30000   ), mk_omsg(  -1500000000 ),
  mk_imsg( -10000,  200000  ), mk_omsg(  -2000000000 ),
]


large_neg_neg_msgs = [
  mk_imsg( -20000,  -100000  ), mk_omsg(   2000000000 ),
  mk_imsg( -30000,  -50000   ), mk_omsg(   1500000000 ),
  mk_imsg( -40000,  -50000   ), mk_omsg(   2000000000 ),
  mk_imsg( -50000,  -30000   ), mk_omsg(   1500000000 ),
  mk_imsg( -10000,  -200000  ), mk_omsg(   2000000000 ),
]


low_order_masked_msgs = [
  mk_imsg( 240, 192 ), mk_omsg(  46080),
  mk_imsg( 65520, 61440 ), mk_omsg(  4025548800 ),
  mk_imsg( 160, 224 ), mk_omsg(  35840 ),
  mk_imsg( 28672, 65280 ), mk_omsg(  1871708160 ),
]


middle_masked_msgs = [
  mk_imsg( 455, 127 ), mk_omsg(  57785 ),
  mk_imsg( 98575, 255 ), mk_omsg(  25136625 ),
  mk_imsg( 4294967055, 68719476752 ), mk_omsg(  4294963440 ),  # Truncated to fit in 32 bits
  mk_imsg( 2725, 2049 ), mk_omsg(  5583525 ),
  mk_imsg( 2863267855, 68719476736 ), mk_omsg( 0 ),  # Truncated to fit in 32 bits
]



sparse_numbers_msgs = [
  mk_imsg( 129, 129 ), mk_omsg(  16641 ),
  mk_imsg( 32769, 32769 ), mk_omsg( 1073807361 ),
  mk_imsg( 8193, 33 ), mk_omsg(  270369 ),
  mk_imsg( 2147483649, 8388609 ), mk_omsg( 2155872257 ),  # Truncated to fit in 32 bits
  mk_imsg( 268439552, 65537 ), mk_omsg( 536875008 ),  # Truncated to fit in 32 bits
]



dense_numbers_msgs = [
  mk_imsg( 254, 254 ), mk_omsg( 64516 ),
  mk_imsg( 65534, 2 ), mk_omsg( 131068 ),
  mk_imsg( 8191, 1023 ), mk_omsg( 8379393 ),
  mk_imsg( 65535, 3 ), mk_omsg( 196605 ),
  mk_imsg( 65535, 65535 ), mk_omsg( 4294836225 ),
]






#-------------------------------------------------------------------------
# Test Case Table
#-------------------------------------------------------------------------

test_case_table = mk_test_case_table([
  (                      "msgs                   src_delay sink_delay"),
  [ "small_pos_pos",     small_pos_pos_msgs,     0,        0          ],
  [ "small_pos_pos",     small_pos_pos_msgs,     1,        1          ],
  [ "small_pos_pos",     small_pos_pos_msgs,     5,        0          ],
  [ "small_pos_pos",     small_pos_pos_msgs,     0,        5          ],
  [ "zero_one_negone",   zero_one_negone_msgs,   0,        0          ],
  [ "small_neg_pos",     small_neg_pos_msgs,     0,        0          ],
  [ "small_pos_neg",     small_pos_neg_msgs,     0,        0          ],
  [ "small_neg_neg",     small_neg_neg_msgs,     0,        0          ],
  [ "large_pos_pos",     large_pos_pos_msgs,     0,        0          ],
  [ "large_pos_neg",     large_pos_neg_msgs,     0,        0          ],
  [ "large_neg_pos",     large_neg_pos_msgs,     0,        0          ],
  [ "large_neg_neg",     large_neg_neg_msgs,     0,        0          ],
  [ "low_order_masked",  low_order_masked_msgs,  0,        0          ],
  [ "middle_masked",     middle_masked_msgs,     0,        0          ],
  [ "sparse_numbers",    sparse_numbers_msgs,    0,        0          ],
  [ "dense_numbers",     dense_numbers_msgs,     0,        0          ],
  [ "dense_numbers",     dense_numbers_msgs,     1,        3          ],


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

