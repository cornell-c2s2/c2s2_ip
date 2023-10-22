import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from src.wishbone.harnesses.wishbone import Wishbone


# Creates a test harness class for the `Wishbone` module.
class Harness(Component):
    def construct(s, harness, n):
        s.harness = harness

        s.src = stream.SourceRTL(mk_bits(n))
        s.sink = stream.SinkRTL(mk_bits(n))

        s.src.send //= s.harness.recv
        s.harness.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# Initialize a simulatable model
def create_model(n):
    model = Wishbone(n)

    # Create a harness wrapping our `Wishbone` module.
    return Harness(model, n)


@pytest.mark.parametrize(
    "bitwidth, other_param",
    [
        (16, 1),
        (32, 1),
    ],
)
def test_simple(request, bitwidth, other_param):
    # The name of the test function run
    test_name = request.node.name

    # Create our model.
    model = create_model(bitwidth)

    model.set_param(
        "top.src.construct",
        # Input values to stream through the block in order
        msgs=[],
        # Cycles to wait after reset before starting to send inputs
        initial_delay=0,
        # Cycles to wait before sending next input (before `send_val` set high)
        interval_delay=0,
    )

    model.set_param(
        "top.sink.construct",
        # Expected output values to read from the block in order
        msgs=[],
        # Cycles to wait after reset before setting `recv_rdy` to high
        initial_delay=0,
        # Cycles to wait between outputs before setting `recv_rdy` to high
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            # Creates the vcd file test_simple_<bitwidth>.vcd for debugging.
            "dump_vcd": f"{test_name}_{bitwidth}",
            # Optional, used to test accurate cycle counts.
            "max_cycles": None,
        },
    )
