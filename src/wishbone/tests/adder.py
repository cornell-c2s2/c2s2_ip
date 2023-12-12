import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from src.wishbone.harnesses.adder import (
    AdderHarness,
)


# Creates a test harness class for the `Wishbone` module.
class Harness(Component):
    def construct(s, harness):
        s.harness = harness

        s.src = stream.SourceRTL(mk_bits(32))
        s.sink = stream.SinkRTL(mk_bits(32))

        s.src.send //= s.harness.recv
        s.harness.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# Initialize a simulatable model
def create_model():
    model = AdderHarness()

    # Create a harness wrapping our `Wishbone` module.
    return Harness(model)

def test_loop(request):
    # The name of the test function run
    test_name = request.node.name
    # Create our model.
    model = create_model()
    model.set_param(
        "top.src.construct",
        # Input values to stream through the block in order
        msgs=[0x0000, 0x0001, 0xeFFF],
        # Cycles to wait after reset before starting to send inputs
        initial_delay=1,
        # Cycles to wait before sending next input (before `send_val` set high)
        interval_delay=1,
    )
    model.set_param(
        "top.sink.construct",
        # Expected output values to read from the block in order
        msgs=[0x0001, 0x0002, 0xF000],
        # Cycles to wait after reset before setting `recv_rdy` to high
        initial_delay=1,
        # Cycles to wait between outputs before setting `recv_rdy` to high
        interval_delay=1,
    )
    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            # Creates the vcd file test_simple.vcd for debugging.
            "dump_vcd": f"{test_name}",
            # Optional, used to test accurate cycle counts.
            "max_cycles": None,
        },
    )