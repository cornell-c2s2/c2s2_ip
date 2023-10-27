# =========================================================================
# IntMulFixedLatRTL_test
# =========================================================================

import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import run_sim
from src.serdes.harnesses.deserializer import DeserializerHarness
from tools.pymtl_extensions import mk_test_matrices, mk_packed

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


class TestHarness(Component):
    def construct(s, BIT_WIDTH=32, N_SAMPLES=8):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH * N_SAMPLES))
        s.deserializer = DeserializerHarness(BIT_WIDTH, N_SAMPLES)

        # Connect

        s.src.send //= s.deserializer.recv
        s.deserializer.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


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
def rand_deserializer():
    n_samples = random.randint(1, 1023)
    # n_bits is capped here because pymtl3 does not support bit widths greater than or equal to 1024
    n_bits = random.randint(1, 1023 // n_samples)
    return (n_samples, n_bits)


def separate_transactions(array, N_SAMPLES, input=True):
    if not input:
        return array[N_SAMPLES :: N_SAMPLES + 1]

    newarray = []
    if input:
        for i in range(0, len(array)):
            if i % (N_SAMPLES + 1) != N_SAMPLES:
                newarray.append(array[i])
        return newarray


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "execution_num": 0,
            "nbits": 1,
            "nsamples": 2,
            "nmsgs": 1,
            "src_delay": 0,
            "sink_delay": 5,
        },
        {
            "execution_num": [0],
            "nbits": [1, 16],
            "nsamples": [1, 2, 16],
            "nmsgs": [1, 100],
            "src_delay": [0, 1, 5],
            "sink_delay": [0, 1, 5],
        },
        {
            "execution_num": list(range(1, 50)),
            "nmsgs": [1, 100],
            "nbits": [None],
            "nsamples": [None],
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
        nsamples, nbits = rand_deserializer()

    th = TestHarness(
        nbits,
        nsamples,
    )

    msgs = create_transactions(nbits, nsamples, p.nmsgs)

    th.set_param(
        "top.src.construct",
        msgs=separate_transactions(msgs, nsamples, True),
        initial_delay=p.src_delay,
        interval_delay=p.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=separate_transactions(msgs, nsamples, False),
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
    )
