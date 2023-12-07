import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from src.arbiter_router.arbiter import Arbiter
from src.arbiter_router.router import Router
from tools.utils import mk_test_matrices, mk_packed

"""
Tests that connect an arbiter to a router and makes sure messages end up in the right place
"""


# Creates a test harness connecting the Arbiter to the Router
class ArbiterRouterTestHarness(Component):
    def construct(s, nbits, nblocks):
        n_addr_bits = (nblocks - 1).bit_length()

        s.arbiter = Arbiter(nbits, nblocks)
        s.router = Router(nbits + n_addr_bits, nblocks)

        # Instantiate models
        s.srcs = [stream.SourceRTL(mk_bits(nbits)) for _ in range(nblocks)]
        s.sinks = [stream.SinkRTL(mk_bits(nbits + n_addr_bits)) for _ in range(nblocks)]

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
        n_addr_bits = (nblocks - 1).bit_length()
        # Arbiter is larger here because the router doesn't clip addresses
        s.arbiter = Arbiter(nbits + n_addr_bits, nblocks)
        s.router = Router(nbits + n_addr_bits, nblocks)

        n_addr_bits = (nblocks - 1).bit_length()

        # Instantiate models
        s.src = stream.SourceRTL(mk_bits(nbits + n_addr_bits))
        # Sink will have doubled address bits
        s.sink = stream.SinkRTL(mk_bits(nbits + 2 * n_addr_bits))

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

    # Bit packer
    n_addr_bits = (nblocks - 1).bit_length()
    pack_addr_data = mk_packed(n_addr_bits, nbits)

    # Add addresses to expected output
    expected_output = [
        [pack_addr_data(i, msg) for msg in msgs[i]] for i in range(nblocks)
    ]

    return (msgs, expected_output)


def router_arbiter_msgs(nbits, nblocks, nmsgs):
    # Bit packer
    n_addr_bits = (nblocks - 1).bit_length()
    pack_addr_data = mk_packed(n_addr_bits, nbits)
    # Packs two versions of the address (as it is duplicated by the arbiter)
    pack_addr_addr_data = mk_packed(n_addr_bits, n_addr_bits, nbits)

    addr_data = [
        (random.randint(0, nblocks - 1), random.randint(0, (1 << nbits) - 1))
        for _ in range(nmsgs)
    ]

    # Random addresses and random data
    msgs = [pack_addr_data(addr, data) for (addr, data) in addr_data]
    # Add the extra address to the expected output
    expected_output = [
        pack_addr_addr_data(addr, addr, data) for (addr, data) in addr_data
    ]

    return msgs, expected_output


spec_matrix = mk_test_matrices(
    {
        "execution_num": 0,
        "nbits": 8,
        "nblocks": 16,
        "nmsgs": 20,
        "src_delay": 0,
        "sink_delay": 0,
    },
    {
        "execution_num": 0,
        "nbits": 8,
        "nblocks": 16,
        "nmsgs": 20,
        "src_delay": 0,
        "sink_delay": 2,
    },
    {
        "execution_num": list(range(1, 11)),  # Do 10 tests
        "nbits": [(8, 32)],  # Test 8-32 bit routers
        "nblocks": [(2, 16)],  # Test 2-16 output routers
        "nmsgs": [50],  # Send 50 messages
        "src_delay": [0, 1, 8],  # Wait this many cycles between inputs
        "sink_delay": [0, 1, 8],  # Wait this many cycles between outputs
        "slow": True,
    },
)


@pytest.mark.parametrize(*spec_matrix)
def test_arbiter_router(p, cmdline_opts):
    random.seed(
        random.random() + p.execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, nblocks = mk_spec(p.nbits, p.nblocks)
    model = ArbiterRouterTestHarness(nbits, nblocks)

    msgs, expected_output = arbiter_router_msgs(nbits, nblocks, p.nmsgs)

    for i in range(nblocks):
        model.set_param(
            f"top.srcs[{i}].construct",
            msgs=msgs[i],
            initial_delay=p.src_delay,
            interval_delay=p.src_delay,
        )

        model.set_param(
            f"top.sinks[{i}].construct",
            msgs=expected_output[i],
            initial_delay=p.sink_delay,
            interval_delay=p.sink_delay,
        )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": p.nmsgs * nblocks * (max(p.src_delay, p.sink_delay) + 1) + 10,
        },
        duts=["arbiter", "router"],
    )


@pytest.mark.parametrize(*spec_matrix)
def test_router_arbiter(p, cmdline_opts):
    random.seed(
        random.random() + p.execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, nblocks = mk_spec(p.nbits, p.nblocks)
    model = RouterArbiterTestHarness(nbits, nblocks)

    msgs, expected_output = router_arbiter_msgs(nbits, nblocks, p.nmsgs * nblocks)

    model.set_param(
        "top.src.construct",
        msgs=msgs,
        initial_delay=p.src_delay,
        interval_delay=p.src_delay,
    )

    model.set_param(
        "top.sink.construct",
        msgs=expected_output,
        initial_delay=p.sink_delay,
        interval_delay=p.sink_delay,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": p.nmsgs * nblocks * (max(p.src_delay, p.sink_delay) + 1) + 10,
        },
        duts=["arbiter", "router"],
    )
