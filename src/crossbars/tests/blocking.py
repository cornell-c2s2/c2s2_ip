# =========================================================================
# Crossbar_test
# =========================================================================

import pytest
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from pymtl3.stdlib import stream
from src.crossbars.blocking import Blocking

class TestHarness(Component):

    def construct(s, BIT_WIDTH: int, N_INPUTS: int, N_OUTPUTS: int, CONTROL_BIT_WIDTH: int):
        # Instantiate models
        s.srcs = [stream.SourceRTL(mk_bits(BIT_WIDTH)) for _ in range(N_INPUTS)]
        s.control = stream.SourceRTL(mk_bits(CONTROL_BIT_WIDTH))
        s.sinks = [stream.SinkRTL(mk_bits(BIT_WIDTH)) for _ in range(N_OUTPUTS)]

        s.dut = Blocking(BIT_WIDTH, N_INPUTS, N_OUTPUTS, CONTROL_BIT_WIDTH)

        # Connect
        for i in range(N_INPUTS):
            s.srcs[i].send //= s.dut.recv[i]
        for i in range(N_OUTPUTS):
            s.dut.send[i] //= s.sinks[i].recv

        s.control.send //= s.dut.control

    def done(s):
        sink_done = False
        src_done = False
        
        for sink in s.sinks:
            if sink.done():
                sink_done = True
                break 
        for src in s.srcs:
            if src.done():
                src_done = True
                break  
        
        return sink_done and src_done

    def line_trace(s):
        srcs_str = "|".join([src.line_trace() for src in s.srcs])
        sinks_str = "|".join([sink.line_trace() for sink in s.sinks])
        return f"{srcs_str} > ({s.dut.line_trace()}) > {sinks_str}"

# -------------------------------------------------------------------------
# Tests
# -------------------------------------------------------------------------
def test_basic():
    return [[2], [[2],[4]], [[4],[0]]]

# -------------------------------------------------------------------------
# Test Case Table
# -------------------------------------------------------------------------
test_case_table = mk_test_case_table([
  (                     "msgs               control_delay  src_delay  sink_delay  BIT_WIDTH  N_INPUTS  N_OUTPUTS  CONTROL_BIT_WIDTH  slow"),
  [ "test_basic",        test_basic,        3,             3,         3,          4,        2,        2,         2,                 False]
])

@pytest.mark.parametrize( **test_case_table )
def test( test_params, cmdline_opts ):

  print(test_params.BIT_WIDTH)
  print(test_params.N_INPUTS)
  print(test_params.N_OUTPUTS) 
  print(test_params.CONTROL_BIT_WIDTH)

  th = TestHarness( test_params.BIT_WIDTH, test_params.N_INPUTS, test_params.N_OUTPUTS, test_params.CONTROL_BIT_WIDTH)

  msgs = test_params.msgs()

  print(msgs[0::3])
  print(msgs[1::3])
  print(msgs[2::3])
  
  th.set_param("top.control.construct",
    msgs=msgs[0],
    initial_delay=test_params.control_delay,
    interval_delay=test_params.control_delay )
  
  for i in range(test_params.N_INPUTS):
    th.set_param(
        f"top.srcs[{i}].construct",
        msgs=msgs[1][i],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay
    )

  for i in range(test_params.N_OUTPUTS):
    th.set_param(
        f"top.sinks[{i}].construct",
        msgs=msgs[2][i],
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

  run_sim( th, cmdline_opts, duts=['dut'] )
