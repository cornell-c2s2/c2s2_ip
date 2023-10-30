import pytest
import random
from pymtl3 import *
from src.arbiter_router.router import Router
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import run_sim
from tools.utils import mk_test_matrix, mk_packed


class TestHarness(Component):
    def construct(s, nbits, noutputs):
        # Instantiate models
        s.src = stream.SourceRTL(mk_bits(nbits))
        s.dut = Router(nbits, noutputs)
        s.sinks = [stream.SinkRTL(mk_bits(nbits)) for _ in range(noutputs)]

        # Connect
        s.src.send //= s.dut.istream
        for i in range(noutputs):
            s.dut.ostream[i] //= s.sinks[i].recv

    def done(s):
        if not s.src.done():
            return False
        for sink in s.sinks:
            if not sink.done():
                return False
        return True

    def line_trace(s):
        sinks_str = "|".join([sink.line_trace() for sink in s.sinks])
        return f"{s.src.line_trace()} > ({s.dut.line_trace()}) > {sinks_str}"


# Creates a random router spec given a range of nbits and noutputs
def router_spec(nbits, noutputs):
    if isinstance(nbits, int):
        nbits = (nbits, nbits)
    if isinstance(noutputs, int):
        noutputs = (noutputs, noutputs)

    # Generate a random number of bits between bounds
    nbits = random.randint(nbits[0], nbits[1])
    # Random number of outputs, guarantees that it fits within nbits
    noutputs = random.randint(noutputs[0], min(noutputs[1], (1 << nbits) - 1))

    return nbits, noutputs


# Creates an input message to the router as well as returning the expected output index
def router_msg(nbits, noutputs):
    # Number of bits needed to represent the output index
    n_addr_bits = (noutputs - 1).bit_length()
    n_data_bits = nbits - n_addr_bits

    addr_bits = mk_bits(n_addr_bits)
    data_bits = mk_bits(n_data_bits)

    # random address and data
    addr = addr_bits(random.randint(0, noutputs - 1))
    data = data_bits(random.randint(0, (1 << n_data_bits) - 1))

    return (concat(addr, data), addr)


@pytest.mark.parametrize(
    "execution_num, nbits, noutputs, nmsgs",
    [
        (0, 8, 16, 20),
        *mk_test_matrix(
            {
                "execution_num": list(range(1, 21)),  # Do 20 tests
                "nbits": [(8, 128)],  # Test 8-32 bit routers
                "noutputs": [(2, 16)],  # Test 2-16 output routers
                "nmsgs": [50],  # Send 50 messages
            },
            slow=True,
        ),
    ],
)
def test_router(execution_num, nbits, noutputs, nmsgs, cmdline_opts):
    random.seed(
        random.random() + execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, noutputs = router_spec(nbits, noutputs)
    model = TestHarness(nbits, noutputs)

    msgs = []
    expected_outputs = [[] for _ in range(noutputs)]
    for _ in range(nmsgs):
        msg, addr = router_msg(nbits, noutputs)
        msgs.append(msg)
        expected_outputs[addr].append(msg)

    model.set_param(
        "top.src.construct",
        msgs=msgs,
        initial_delay=0,
        interval_delay=0,
    )

    for i in range(noutputs):
        model.set_param(
            f"top.sinks[{i}].construct",
            msgs=expected_outputs[i],
            initial_delay=0,
            interval_delay=0,
        )

    run_sim(model, cmdline_opts, duts=["dut"])
