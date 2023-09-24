# =========================================================================
# IntMulFixedLatRTL_test
# =========================================================================

import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.serdes.harnesses.deserializer import DeserializerTestHarnessVRTL

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


class TestHarness(Component):
    def construct(s, deserializer, BIT_WIDTH=32, N_SAMPLES=8):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH * N_SAMPLES))
        s.deserializer = deserializer

        # Connect

        s.src.send //= s.deserializer.recv
        s.deserializer.send //= s.sink.recv

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


# ----------------------------------------------------------------------
# Test Case Table
# ----------------------------------------------------------------------


def eight_point(BIT_WIDTH, N_SAMPLES):
    return [
        0x00000008,
        0x00000007,
        0x00000006,
        0x00000005,
        0x00000004,
        0x00000003,
        0x00000002,
        0x00000001,
        0x0000000100000002000000030000000400000005000000060000000700000008,
    ]


def eight_point_two_transaction(BIT_WIDTH, N_SAMPLES):
    return [
        0x00000008,
        0x00000007,
        0x00000006,
        0x00000005,
        0x00000004,
        0x00000003,
        0x00000002,
        0x00000001,
        0x0000000100000002000000030000000400000005000000060000000700000008,
        0x00000001,
        0x00000002,
        0x00000003,
        0x00000004,
        0x00000005,
        0x00000006,
        0x00000007,
        0x00000008,
        0x0000000800000007000000060000000500000004000000030000000200000001,
    ]


def create_transactions(BIT_WIDTH, N_SAMPLES, N_QUERIES):
    def pack_transaction(vals):
        total = 0
        for i in vals[::-1]:
            total *= 2**BIT_WIDTH
            total += i
        return vals + [total]

    return sum(
        [
            pack_transaction(
                [random.randrange(0, 2**BIT_WIDTH) for __ in range(N_SAMPLES)]
            )
            for _ in range(N_QUERIES)
        ],
        [],
    )


def create_transaction_lmbda(N_QUERIES):
    return lambda BIT_WIDTH, N_SAMPLES: create_transactions(
        BIT_WIDTH, N_SAMPLES, N_QUERIES
    )


test_case_table = mk_test_case_table(
    [
        (
            "msgs                                       src_delay sink_delay BIT_WIDTH N_SAMPLES"
        ),
        ["eight_point", eight_point, 0, 0, 32, 8],
        ["eight_point_two_transaction", eight_point_two_transaction, 0, 0, 32, 8],
        *[
            [
                "random_transaction",
                create_transaction_lmbda(n_queries),
                0,
                0,
                8,
                n_samples,
            ]
            for n_samples in [4, 8, 16, 32, 64]
            for n_queries in [1, 2]
        ],
    ]
)


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


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        DeserializerTestHarnessVRTL(test_params.BIT_WIDTH, test_params.N_SAMPLES),
        test_params.BIT_WIDTH,
        test_params.N_SAMPLES,
    )

    msgs = test_params.msgs(test_params.BIT_WIDTH, test_params.N_SAMPLES)

    th.set_param(
        "top.src.construct",
        msgs=separate_transactions(msgs, test_params.N_SAMPLES, True),
        initial_delay=test_params.src_delay + 3,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=separate_transactions(msgs, test_params.N_SAMPLES, False),
        initial_delay=test_params.sink_delay + 3,
        interval_delay=test_params.sink_delay,
    )

    run_sim(th, cmdline_opts, duts=["deserializer"])
