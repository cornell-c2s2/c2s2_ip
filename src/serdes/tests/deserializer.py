# =========================================================================
# IntMulFixedLatRTL_test
# =========================================================================

import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import run_sim
from src.serdes.deserializer import DeserializerWrapper
from tools.utils import mk_test_matrices, mk_list_bitstruct

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


class TestHarness(Component):
    def construct(s, BIT_WIDTH, N_SAMPLES):
        # Instantiate models

        s.dut = DeserializerWrapper(BIT_WIDTH, N_SAMPLES)
        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_list_bitstruct(BIT_WIDTH, N_SAMPLES))

        # Connect
        s.src.send //= s.dut.recv
        s.dut.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

    def line_trace(s):
        return (
            s.src.line_trace()
            + " > "
            + s.deserializer.line_trace()
            + " > "
            + s.sink.line_trace()
        )


# Creates a list of `nmsgs` random transactions
# for a deserializer with `nbits` bits and `nsamples` samples
def create_transactions(nbits, nsamples, nmsgs):
    def pack_transaction(vals):
        packer = mk_packed(*([nbits] * nsamples))

        bits = packer(*vals[::-1])
        # Duplicate the transaction, one for input and output
        return vals + [bits]

    return sum(
        [
            pack_transaction(
                [random.randint(0, (1 << nbits) - 1) for __ in range(nsamples)]
            )
            for _ in range(nmsgs)
        ],
        [],
    )


# Return a random deserializer spec
def rand_deserializer(max_bus=1024):
    n_samples = random.randint(1, max_bus - 1)
    # n_bits is capped here because pymtl3 does not support bit widths greater than or equal to 1024
    n_bits = random.randint(1, (max_bus - 1) // n_samples)
    return (n_samples, n_bits)


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "execution_num": [0],
            "nbits": [1, 16],
            "nsamples": [1, 2, 16],
            "nmsgs": [1, 100],
            "src_delay": [0, 1, 5],
            "sink_delay": [0, 1, 5],
        },
        {
            "execution_num": list(range(1, 10)),
            "nmsgs": 100,
            "nbits": None,
            "nsamples": None,
            "src_delay": [0, 1, 5],
            "sink_delay": [0, 1, 5],
            "slow": True,
        },
    )
)
def test_deserializer(p, cmdline_opts):
    random.seed(random.random() + p.execution_num)

    nbits = p.nbits
    nsamples = p.nsamples
    nmsgs = p.nmsgs

    if nbits is None or nsamples is None:
        nsamples, nbits = rand_deserializer(256)

    th = TestHarness(
        nbits,
        nsamples,
    )

    msgs = create_transactions(nbits, nsamples, p.nmsgs)

    mk_ret = mk_list_bitstruct(nbits, nsamples)

    th.set_param(
        "top.src.construct",
        msgs=sum(msgs, []),
        initial_delay=p.src_delay,
        interval_delay=p.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=[mk_ret(msg) for msg in msgs],
        initial_delay=p.sink_delay,
        interval_delay=p.sink_delay,
    )

    run_sim(
        th,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": nmsgs * (nsamples + 1) * (1 + max(p.src_delay, p.sink_delay))
            + 10,
        },
        duts=["dut"],
    )
