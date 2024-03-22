import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import run_sim
from src.serdes.serializer import SerializerWrapper
from src.serdes.tests.utils import create_transactions, rand_spec
from tools.utils import mk_list_bitstruct, mk_test_matrices, mk_packed


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


class TestHarness(Component):
    def construct(s, BIT_WIDTH, N_SAMPLES):
        # Instantiate models

        s.src = stream.SourceRTL(mk_list_bitstruct(mk_bits(BIT_WIDTH), N_SAMPLES))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.dut = SerializerWrapper(BIT_WIDTH, N_SAMPLES)

        # Connect

        s.src.send //= s.dut.recv
        s.dut.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

    def line_trace(s):
        return (
            s.src.line_trace()
            + " > "
            + s.dut.line_trace()
            + " > "
            + s.sink.line_trace()
        )


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "execution_num": [0],
            "nbits": [4],
            "nsamples": [1, 2, 8],
            "nmsgs": [50],
            "src_delay": [0, 1, 5],
            "sink_delay": [0, 1, 5],
        },
        {
            "execution_num": [0],
            "nbits": [16, 32],
            "nsamples": [1, 2, 8],
            "nmsgs": [50],
            "src_delay": [0, 1, 5],
            "sink_delay": [0, 1, 5],
        },
        {
            "execution_num": list(range(1, 5)),
            "nmsgs": 50,
            "nbits": None,
            "nsamples": None,
            "src_delay": [0, 1, 5],
            "sink_delay": [0, 1, 5],
            "slow": True,
        },
    )
)
def test_serializer(p, cmdline_opts):
    random.seed(random.random() + p.execution_num)

    nsamples = p.nsamples
    nbits = p.nbits
    nmsgs = p.nmsgs

    if nbits is None or nsamples is None:
        nsamples, nbits = rand_spec(128)

    th = TestHarness(
        nbits,
        nsamples,
    )

    msgs = create_transactions(nbits, nsamples, nmsgs)

    mk_msg = mk_list_bitstruct(mk_bits(nbits), nsamples)

    th.set_param(
        "top.src.construct",
        msgs=[mk_msg(msg) for msg in msgs],
        initial_delay=p.src_delay,
        interval_delay=p.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=sum(msgs, []),
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
        duts=["dut.dut"],
    )
