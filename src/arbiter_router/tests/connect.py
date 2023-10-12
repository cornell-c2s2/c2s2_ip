import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from src.arbiter_router.harnesses.arbiter import Arbiter
from src.arbiter_router.harnesses.router import Router
from tools.pymtl_extensions import mk_test_matrix

"""
Tests that connect an arbiter to a router and makes sure messages end up in the right place
"""


# Creates a test harness connecting the Arbiter to the Router
class TestHarness(Component):
    def construct(s, nbits, nblocks):
        s.arbiter = Arbiter(nbits, nblocks)
        s.router = Router(nbits, nblocks)

        # Instantiate models
        s.srcs = [stream.SourceRTL(mk_bits(nbits)) for _ in range(nblocks)]
        s.sinks = [stream.SinkRTL(mk_bits(nbits)) for _ in range(nblocks)]

        # Connect arbiter to router
        s.arbiter.ostream //= s.router.istream

        # Connect sources and sinks
        for i in range(nblocks):
            s.srcs[i].send //= s.arbiter.istream[i]
            s.router.ostream[i] //= s.sinks[i].recv

    def done(s):
        for sink in s.sinks:
            if not sink.done():
                return False
        for src in s.srcs:
            if not src.done():
                return False
        return True

    def line_trace(s):
        srcs_str = "|".join([src.line_trace() for src in s.srcs])
        sinks_str = "|".join([sink.line_trace() for sink in s.sinks])
        return f"{srcs_str} > ({s.arbiter.line_trace()}) > ({s.router.line_trace()}) > {sinks_str}"


# Creates a random spec given a range of nbits and nblocks
def mk_spec(nbits, nblocks):
    if isinstance(nbits, int):
        nbits = (nbits, nbits)
    if isinstance(nblocks, int):
        nblocks = (nblocks, nblocks)

    # Generate a random number of bits between bounds
    nbits = random.randint(nbits[0], nbits[1])
    # Random number of outputs, guarantees that it fits within nbits
    nblocks = random.randint(nblocks[0], nblocks[1])

    return nbits, nblocks


def sim_msgs(nbits, nblocks, nmsgs):
    # Create a bunch of messages
    msgs = [
        [random.randint(0, (1 << nbits) - 1) for _ in range(nmsgs)]
        for _ in range(nblocks)
    ]

    # Output should be identical to input
    return msgs


# Simple arbiter tests where inputs are sent every `delay+1` cycles
@pytest.mark.parametrize(
    "execution_num, nbits, nblocks, nmsgs, delay",
    [
        (0, 8, 4, 20, 0),
        (0, 8, 4, 20, 2),
        *mk_test_matrix(
            {
                "execution_num": list(range(1, 21)),  # Do 20 tests
                "nbits": [(8, 32)],  # Test 8-32 bit routers
                "nblocks": [(2, 16)],  # Test 2-16 input routers
                "nmsgs": [100],  # Send 100 messages
                "delay": [0, 1, 3, 16],  # Wait this many cycles between inputs
            },
            slow=True,
        ),
    ],
)
def test_arbiter(execution_num, nbits, nblocks, nmsgs, delay, cmdline_opts):
    random.seed(
        random.random() + execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, nblocks = mk_spec(nbits, nblocks)
    model = TestHarness(nbits, nblocks)

    msgs = sim_msgs(nbits, nblocks, nmsgs)

    for i in range(nblocks):
        model.set_param(
            f"top.srcs[{i}].construct",
            msgs=msgs[i],
            initial_delay=0,
            interval_delay=delay,
        )

        model.set_param(
            f"top.sinks[{i}].construct",
            msgs=msgs[i],
            initial_delay=0,
            interval_delay=delay,
        )

    run_sim(model, cmdline_opts)
