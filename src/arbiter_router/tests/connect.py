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
class ArbiterRouterTestHarness(Component):
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


# Test harness hooking up the router first to the arbiter
class RouterArbiterTestHarness(Component):
    def construct(s, nbits, nblocks):
        s.arbiter = Arbiter(nbits, nblocks)
        s.router = Router(nbits, nblocks)

        n_addr_bits = (nblocks - 1).bit_length()

        # Instantiate models
        s.src = stream.SourceRTL(mk_bits(nbits + n_addr_bits))
        s.sink = stream.SinkRTL(mk_bits(nbits + n_addr_bits))

        # Connect arbiter to router
        for i in range(nblocks):
            s.router.ostream[i] //= s.arbiter.istream[i]

        # Connect source and sink
        s.src.send //= s.router.istream
        s.arbiter.ostream //= s.sink.recv

    def done(s):
        return s.sink.done() and s.src.done()

    def line_trace(s):
        return f"{s.src.line_trace()} > ({s.arbiter.line_trace()}) > ({s.router.line_trace()}) > {s.sink.line_trace()}"


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


def arbiter_router_msgs(nbits, nblocks, nmsgs):
    # Create a bunch of messages
    msgs = [
        [random.randint(0, (1 << nbits) - 1) for _ in range(nmsgs)]
        for _ in range(nblocks)
    ]

    # Output should be identical to input
    return msgs


def router_arbiter_msgs(nbits, nblocks, nmsgs):
    # Create a bunch of messages
    msgs = [
        (random.randint(0, nblocks - 1) << nbits)  # Random address
        | random.randint(0, (1 << nbits) - 1)  # Random data
        for _ in range(nmsgs)
    ]

    # Output should be identical to input
    return msgs


spec_matrix = [
    (0, 8, 4, 20, 0),
    (0, 8, 4, 20, 2),
    *mk_test_matrix(
        {
            "execution_num": list(range(1, 21)),  # Do 20 tests
            "nbits": [(8, 32)],  # Test 8-32 bit routers
            "nblocks": [(2, 16)],  # Test 2-16 input routers
            "nmsgs": [50],  # Send 50 messages
            "delay": [0, 1, 16],  # Wait this many cycles between inputs
        },
        slow=True,
    ),
]


@pytest.mark.parametrize("execution_num, nbits, nblocks, nmsgs, delay", spec_matrix)
def test_arbiter_router(execution_num, nbits, nblocks, nmsgs, delay, cmdline_opts):
    random.seed(
        random.random() + execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, nblocks = mk_spec(nbits, nblocks)
    model = ArbiterRouterTestHarness(nbits, nblocks)

    msgs = arbiter_router_msgs(nbits, nblocks, nmsgs)

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

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": nmsgs * nblocks * (delay + 1) + 10,
        },
    )


@pytest.mark.parametrize("execution_num, nbits, nblocks, nmsgs, delay", spec_matrix)
def test_router_arbiter(execution_num, nbits, nblocks, nmsgs, delay, cmdline_opts):
    random.seed(
        random.random() + execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, nblocks = mk_spec(nbits, nblocks)
    model = RouterArbiterTestHarness(nbits, nblocks)

    msgs = router_arbiter_msgs(nbits, nblocks, nmsgs * nblocks)

    model.set_param(
        "top.src.construct",
        msgs=msgs,
        initial_delay=0,
        interval_delay=delay,
    )

    model.set_param(
        "top.sink.construct",
        msgs=msgs,
        initial_delay=0,
        interval_delay=delay,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": nmsgs * nblocks * (delay + 1) + 10,
        },
    )
