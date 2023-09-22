#=========================================================================
# IntMulFixedLatRTL_test
#=========================================================================

import pytest
import random

random.seed(0xdeadbeef)

from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from serializer.SerializerTestHarnessRTL import SerializerTestHarnessVRTL
from fxpmath import Fxp
import numpy as np
import math


#-------------------------------------------------------------------------
# TestHarness
#-------------------------------------------------------------------------


class TestHarness( Component ):

  def construct( s, serializer, BIT_WIDTH = 32, N_SAMPLES = 8):

    # Instantiate models

    s.src  = stream.SourceRTL( mk_bits(BIT_WIDTH * N_SAMPLES) )
    s.sink = stream.SinkRTL  ( mk_bits(BIT_WIDTH ) )
    s.serializer = serializer

    # Connect

    s.src.send  //= s.serializer.recv
    s.serializer.send //= s.sink.recv

  def done( s ):
    return s.src.done() and s.sink.done()

  def line_trace( s ):
    return s.src.line_trace() + " > " + s.serializer.line_trace() + " > " + s.sink.line_trace()

def packed_msg(array, bitwidth, size): #Array of ints
  input = Bits(1)
  bit_convert = mk_bits(bitwidth)
  output = input
  for i in range(len(array)):

    output = concat( bit_convert(array[i]), output )
  
  output = output[1:bitwidth * fft_size + 1]
  
  return output

#----------------------------------------------------------------------
# Test Case Table
#----------------------------------------------------------------------

def eight_point():
    return [0x0000000100000002000000030000000400000005000000060000000700000008, 
            0x00000008, 0x00000007, 0x00000006, 0x00000005, 0x00000004, 0x00000003, 0x00000002, 0x00000001]

def eight_point_two_packet():
    return [0x0000000100000002000000030000000400000005000000060000000700000008, 
            0x00000008, 0x00000007, 0x00000006, 0x00000005, 0x00000004, 0x00000003, 0x00000002, 0x00000001,
            0x0000000800000007000000060000000500000004000000030000000200000001, 
            0x00000001, 0x00000002, 0x00000003, 0x00000004, 0x00000005, 0x00000006, 0x00000007, 0x00000008,
            0x0000000000000000000000000000000000000000000000000000000000000000, 
            0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000]
            
def eight_point_three_packet(): #test to have multiple transactions 
    return [0x0000000100000002000000030000000400000005000000060000000700000008, 
            0x00000008, 0x00000007, 0x00000006, 0x00000005, 0x00000004, 0x00000003, 0x00000002, 0x00000001,
            0x00000008000000070000000600000005000000AA000000030000000200000001, 
            0x00000001, 0x00000002, 0x00000003, 0x000000AA, 0x00000005, 0x00000006, 0x00000007, 0x00000008,
            0x0000000800000007000000060000000500000004000000030034000200000001,
            0x00000001, 0x000340002, 0x00000003, 0x00000004, 0x00000005, 0x00000006, 0x00000007, 0x00000008] 

def sixteen_point():       
    return [0x00000001000000020000000300000004000000050000000600000007000000080000000100000002000000030000000400000005000000060000000700000008, 
            0x00000008, 0x00000007, 0x00000006, 0x00000005, 0x00000004, 0x00000003, 0x00000002, 0x00000001,
            0x00000008, 0x00000007, 0x00000006, 0x00000005, 0x00000004, 0x00000003, 0x00000002, 0x00000001]

def thirtytwo_point(): 
    return [0x12345678_123E5678_F23456F8_123456BA, 
            0xA, 0xB, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0x8, 0xF, 0x6, 0x5, 0x4, 0x3, 0x2, 0xF,  
            0x8, 0x7, 0x6, 0x5, 0xE, 0x3, 0x2, 0x1,
            0x8, 0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1]

def sixtyfour_point(): 
    return [0x12345678_123E5678_F23456F8_123456BA_12345678_123E5678_F23456F8_123456BA,
            0xA, 0xB, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0x8, 0xF, 0x6, 0x5, 0x4, 0x3, 0x2, 0xF,  
            0x8, 0x7, 0x6, 0x5, 0xE, 0x3, 0x2, 0x1,
            0x8, 0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1, 
            0xA, 0xB, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0x8, 0xF, 0x6, 0x5, 0x4, 0x3, 0x2, 0xF,  
            0x8, 0x7, 0x6, 0x5, 0xE, 0x3, 0x2, 0x1,
            0x8, 0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1]

def onetwentyeight_point(): 
    return [0x12345678_123E5678_F23456F8_123456BA_12345678_123E5678_F23456F8_123456BA_12345678_123E5678_F23456F8_123456BA_12345678_123E5678_F23456F8_123456BA,
            0xA, 0xB, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0x8, 0xF, 0x6, 0x5, 0x4, 0x3, 0x2, 0xF,  
            0x8, 0x7, 0x6, 0x5, 0xE, 0x3, 0x2, 0x1,
            0x8, 0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1, 
            0xA, 0xB, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0x8, 0xF, 0x6, 0x5, 0x4, 0x3, 0x2, 0xF,  
            0x8, 0x7, 0x6, 0x5, 0xE, 0x3, 0x2, 0x1,
            0x8, 0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0xA, 0xB, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0x8, 0xF, 0x6, 0x5, 0x4, 0x3, 0x2, 0xF,  
            0x8, 0x7, 0x6, 0x5, 0xE, 0x3, 0x2, 0x1,
            0x8, 0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1, 
            0xA, 0xB, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1,
            0x8, 0xF, 0x6, 0x5, 0x4, 0x3, 0x2, 0xF,  
            0x8, 0x7, 0x6, 0x5, 0xE, 0x3, 0x2, 0x1,
            0x8, 0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1]

def twofiftysix_point(): 
    return [0b01000001_00100000_10000100_00100010_01000001_00100000_10000100_00100010_01000001_00100000_10000100_00100010_01000001_00100000_10000100_00100010_01000001_00100000_10000100_00100010_01000001_00100000_10000100_00100010_01000001_00100000_10000100_00100010_01000001_00100000_10000100_00100010, 
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0,
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0,
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0,
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0,
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0,
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0,
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0,
            0b0, 0b1, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b0, 0b0, 0b1, 0b0, 0b0, 0b0, 0b0, 0b1,  
            0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0, 0b0,
            0b1, 0b0, 0b0, 0b0, 0b0, 0b0, 0b1, 0b0]


test_case_table = mk_test_case_table([
  (                                   "msgs                                       src_delay sink_delay BIT_WIDTH N_SAMPLES"),
  [ "eight_point",                     eight_point,                               0,        0,         32,       8         ],
  [ "eight_point_two_packet",          eight_point_two_packet,                    0,        0,         32,       8         ],
  [ "sixteen_point",                   sixteen_point,                             0,        0,         32,       16        ],
  [ "thirtytwo_point",                 thirtytwo_point,                           0,        0,         4,        32        ],
  [ "sixtyfour_point",                 sixtyfour_point,                           0,        0,         4,        64        ],
  [ "onetwentyeight_point",            onetwentyeight_point,                      0,        0,         4,        128       ],
  [ "twofiftysix_point",               twofiftysix_point,                         0,        0,         1,        256       ],
])

def separate_transactions(array, N_SAMPLES, input = True):
  
  if(input): 
    return array[0::N_SAMPLES + 1]

  newarray = []
  if (not input): 
    for i in range(1, len(array)):
      if(i % (N_SAMPLES + 1) != 0):
        newarray.append(array[i])
    return newarray
  

#-------------------------------------------------------------------------
# TestHarness
#-------------------------------------------------------------------------

@pytest.mark.parametrize( **test_case_table )
def test( test_params, cmdline_opts ):

  th = TestHarness( SerializerTestHarnessVRTL(test_params.BIT_WIDTH, test_params.N_SAMPLES), test_params.BIT_WIDTH, test_params.N_SAMPLES )

  msgs = test_params.msgs()

  th.set_param("top.src.construct",
    msgs=separate_transactions(msgs,test_params.N_SAMPLES,True),
    initial_delay=test_params.src_delay+3,
    interval_delay=test_params.src_delay )

  th.set_param("top.sink.construct",
    msgs=separate_transactions(msgs,test_params.N_SAMPLES,False),
    initial_delay=test_params.sink_delay+3,
    interval_delay=test_params.sink_delay )

  run_sim( th, cmdline_opts, duts=['serializer'] )
