import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim, config_model_with_cmdline_opts
from pymtl3.stdlib import stream
from src.arbiter_router.arbiter import Arbiter
from tools.utils import mk_test_matrices


# Creates a test harness class for the `Arbiter` module.
class TestHarness(Component):
    def construct(s, nbits, ninputs):
        # Instantiate models
        s.srcs = [stream.SourceRTL(mk_bits(nbits)) for _ in range(ninputs)]
        s.dut = Arbiter(nbits, ninputs)
        s.sink = stream.SinkRTL(mk_bits(nbits + (ninputs - 1).bit_length()))

        # Connect
        s.dut.ostream //= s.sink.recv
        for i in range(ninputs):
            s.srcs[i].send //= s.dut.istream[i]

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


# Creates a random arbiter spec given a range of nbits and ninputs
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
    mk_nbits = mk_bits(nbits)
    mk_n_addr_bits = mk_bits((ninputs - 1).bit_length())
    # Create a bunch of messages
    msgs = [
        [mk_nbits(random.randint(0, (1 << nbits) - 1)) for _ in range(nmsgs)]
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
                expected_output.append(
                    concat(mk_n_addr_bits(i), msgs[i][msg_indices[i]])
                )
                msg_indices[i] += 1
                enabled[i] = False
                break

        # Done check
        if all(msg_index >= nmsgs for msg_index in msg_indices):
            break

        cycle += 1

    return (msgs, expected_output)


# Simple arbiter tests where inputs are sent every `delay+1` cycles
@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "execution_num": 0,
            "nbits": 8,
            "ninputs": 4,
            "nmsgs": 20,
            "delay": 0,
        },
        {
            "execution_num": 0,
            "nbits": 8,
            "ninputs": 4,
            "nmsgs": 20,
            "delay": 2,
        },
        {
            "execution_num": list(range(1, 11)),  # Do 10 tests
            "nbits": [(8, 32)],  # Test 8-32 bit arbiters
            "ninputs": [(2, 16)],  # Test 2-16 input arbiters
            "nmsgs": [50],  # Send 50 messages
            "delay": [0, 1, 8],  # Wait this many cycles between inputs
            "slow": True,
        },
    )
)
def test_arbiter(p, cmdline_opts):
    random.seed(
        random.random() + p.execution_num
    )  # Done so each test has a deterministic but different random seed
    nbits, ninputs = arbiter_spec(p.nbits, p.ninputs)
    model = TestHarness(nbits, ninputs)

    msgs, expected_output = sim_arbiter(nbits, ninputs, p.nmsgs, p.delay)

    for i in range(ninputs):
        model.set_param(
            f"top.srcs[{i}].construct",
            msgs=msgs[i],
            initial_delay=p.delay,
            interval_delay=p.delay,
        )

    # Would need an unordered sink to test delays here
    model.set_param(
        "top.sink.construct",
        msgs=expected_output,
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(model, cmdline_opts, duts=["dut"])
