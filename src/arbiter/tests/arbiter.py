import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from src.arbiter.harnesses.arbiter import Arbiter
from tools.pymtl_extensions import mk_test_matrix


# Creates a test harness class for the `Arbiter` module.
class TestHarness(Component):
    def construct(s, nbits, ninputs):
        # Instantiate models
        s.srcs = [stream.SourceRTL(mk_bits(nbits)) for _ in range(ninputs)]
        s.dut = Arbiter(nbits, ninputs)
        s.sink = stream.SinkRTL(mk_bits(nbits))

        # Connect
        s.dut.istream //= s.sink.recv
        for i in range(ninputs):
            s.srcs[i].send //= s.dut.ostreams[i]

    def done(s):
        if not s.sink.done():
            return False
        for src in s.srcs:
            if not src.done():
                return False
        return True

    def line_trace(s):
        srcs_str = "|".join([src.line_trace() for src in s.srcs])
        return f"{srcs_str} > ({s.dut.line_trace()}) > {s.sink.line_trace()}"


# Creates a random router spec given a range of nbits and ninputs
def arbiter_spec(nbits, ninputs):
    if isinstance(nbits, int):
        nbits = (nbits, nbits)
    if isinstance(ninputs, int):
        ninputs = (ninputs, ninputs)

    # Generate a random number of bits between bounds
    nbits = random.randint(nbits[0], nbits[1])
    # Random number of outputs, guarantees that it fits within nbits
    ninputs = random.randint(ninputs[0], ninputs[1])

    return nbits, ninputs


def sim_arbiter(nbits, ninputs, nmsgs, delay):
    # Create a bunch of messages
    msgs = [
        [random.randint(0, (1 << nbits) - 1) for _ in range(nmsgs)]
        for _ in range(ninputs)
    ]

    # Which input are we at for each sender
    msg_indices = [0 for _ in range(ninputs)]
    enabled = [False for _ in range(ninputs)]

    expected_output = []
    cycle = 0
    while True:
        if cycle % (delay + 1) == 0:
            # Send inputs every `delay+1` cycles
            for i in range(ninputs):
                if not enabled[i] and msg_indices[i] < nmsgs:
                    enabled[i] = True

        # Send inputs from LSB to MSB
        for i in range(ninputs):
            if enabled[i]:
                expected_output.append(msgs[i][msg_indices[i]])
                msg_indices[i] += 1
                enabled[i] = False
                break

        # Done check
        if all(msg_index >= nmsgs for msg_index in msg_indices):
            break

    return (msgs, expected_output)


# Simple arbiter tests where inputs are sent every `delay+1` cycles
@pytest.mark.parametrize(
    "execution_num, nbits, ninputs, nmsgs",
    [
        (0, 8, 4, 20),
        *mk_test_matrix(
            {
                "execution_num": list(range(1, 101)),  # Do 100 tests
                "nbits": [(8, 32)],  # Test 8-128 bit routers
                "ninputs": [(2, 16)],  # Test 2-16 input routers
                "nmsgs": [100],  # Send 100 messages
                "delay": [0, 1, 3, 16],  # Wait this many cycles between inputs
            },
            slow=True,
        ),
    ],
)
def test_arbiter(execution_num, nbits, ninputs, nmsgs, delay, cmdline_opts):
    random.seed(
        random.random() + execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, ninputs = arbiter_spec(nbits, ninputs)
    model = TestHarness(nbits, ninputs)

    msgs, expected_output = sim_arbiter(nbits, ninputs, nmsgs, delay)

    for i in range(ninputs):
        model.set_param(
            f"top.srcs[{i}].construct",
            msgs=msgs[i],
            initial_delay=0,
            interval_delay=delay,
        )

    model.set_param(
        "top.sink.construct",
        msgs=expected_output,
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(model, cmdline_opts)
