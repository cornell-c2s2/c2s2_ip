import pytest
from pymtl3 import *
from pymtl3.stdlib.test_utils import run_test_vector_sim
from src.fft.pease.harnesses.stride_permutation import StridePermutation
from tools.pymtl_extensions import mk_test_matrix


# Make the names of the input ports
def mk_header(n):
    return (
        (
            " ".join([f"recv[{i}]" for i in range(n)])
            + " "
            + " ".join([f"send[{i}]*" for i in range(n)])
        ),
    )


# Creates a test case for a 2*l length stride permutation
def stride_perm(l, n):
    b = mk_bits(n)
    data = [b(i) for i in range(n)]
    expected = [
        *[b(i * 2) for i in range(n // 2)],
        *[b(i * 2 + 1) for i in range(n // 2)],
    ]

    return [mk_header(n), [*data, *expected]]


def test_simple():
    run_test_vector_sim(
        StridePermutation(8, 32),
        [
            mk_header(8),
            [
                *[Bits32(i) for i in [0, 1, 2, 3, 4, 5, 6, 7]],
                *[Bits32(i) for i in [0, 2, 4, 6, 1, 3, 5, 7]],
            ],
        ],
        cmdline_opts={},
    )


@pytest.mark.parametrize("l,n", mk_test_matrix({"l": [2, 4, 6, 32], "n": [32, 16]}))
def test_stride_perm(l, n):
    run_test_vector_sim(
        StridePermutation(l, n),
        stride_perm(l, n),
        cmdline_opts={},
    )
