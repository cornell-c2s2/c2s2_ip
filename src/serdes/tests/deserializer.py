# =========================================================================
# IntMulFixedLatRTL_test
# =========================================================================

import pytest
import random
from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import run_sim
from src.serdes.deserializer import DeserializerWrapper
from tools.utils import mk_test_case_table, mk_list_bitstruct

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


# ----------------------------------------------------------------------
# Test Case Table
# ----------------------------------------------------------------------


def eight_point_two_transaction(BIT_WIDTH, N_SAMPLES):
    return [
        [
            0x00000008,
            0x00000007,
            0x00000006,
            0x00000005,
            0x00000004,
            0x00000003,
            0x00000002,
            0x00000001,
        ],
        [
            0x00000001,
            0x00000002,
            0x00000003,
            0x00000004,
            0x00000005,
            0x00000006,
            0x00000007,
            0x00000008,
        ],
    ]


# Creates a list of `N_QUERIES` random transactions
# for a deserializer with `BIT_WIDTH` bits and `N_SAMPLES` samples
def create_transactions(BIT_WIDTH, N_SAMPLES, N_QUERIES):
    return [
        [random.randint(0, (1 << BIT_WIDTH) - 1) for __ in range(N_SAMPLES)]
        for _ in range(N_QUERIES)
    ]


# Returns a function that takes the number of bits and number of samples
# and creates a list of `N_QUERIES` random transactions
def create_transaction_lmbda(N_QUERIES):
    return lambda BIT_WIDTH, N_SAMPLES: create_transactions(
        BIT_WIDTH, N_SAMPLES, N_QUERIES
    )


# Return `N_SAMPLES and `BIT_WIDTH` for `n` random deserializers
def random_deserializers(n):
    for _ in range(n):
        n_samples = random.randint(2, 128)
        # n_bits is capped here because pymtl3 does not support bit widths greater than or equal to 1024
        n_bits = random.randint(1, 1023 // n_samples)
        yield (n_samples, n_bits)


test_case_table = mk_test_case_table(
    [
        ("msgs src_delay sink_delay BIT_WIDTH N_SAMPLES slow"),
        [
            "eight_point_two_transaction",
            eight_point_two_transaction,
            0,
            0,
            32,
            8,
            False,
        ],
        *[
            [
                "random_transaction",
                create_transaction_lmbda(n_queries),
                0,
                0,
                n_bits,
                n_samples,
                True,
            ]
            # Creates a test case for each combination of (n_samples, n_bits) and n_queries
            for (n_samples, n_bits) in [
                (2, 128),
                (2, 64),
                (8, 32),
                (16, 32),
                (32, 16),
                (64, 8),
                (128, 4),
                (256, 2),
                *random_deserializers(100),
            ]
            for n_queries in [1, 2, 100]
        ],
    ]
)

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------


@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        test_params.BIT_WIDTH,
        test_params.N_SAMPLES,
    )

    msgs = test_params.msgs(test_params.BIT_WIDTH, test_params.N_SAMPLES)

    mk_ret = mk_list_bitstruct(test_params.BIT_WIDTH, test_params.N_SAMPLES)

    th.set_param(
        "top.src.construct",
        msgs=sum(msgs, []),
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=[mk_ret(msg) for msg in msgs],
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

    run_sim(
        th,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": len(msgs) + 10,
        },
        duts=["dut"],
    )
