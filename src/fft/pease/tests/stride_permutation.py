import pytest
from pymtl3 import Bits32, mk_bits
from pymtl3.stdlib.test_utils import run_test_vector_sim
from src.fft.pease.helpers.stride_permutation import StridePermutation
from src.fft.pease.sim import stride_permutation
from tools.utils import mk_test_matrices


# Make the names of the input ports
def mk_header(nsamples):
    return (
        (
            " ".join([f"recv[{i}]" for i in range(nsamples)])
            + " "
            + " ".join([f"send[{i}]*" for i in range(nsamples)])
        ),
    )


# Creates a test case for a 2*l length stride permutation
def stride_perm(nsamples, nbits):
    b = mk_bits(nbits)
    data = [b(i) for i in range(nsamples)]
    expected = stride_permutation(nsamples, data)

    return [mk_header(nsamples), [*data, *expected]]


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


@pytest.mark.parametrize(
    *mk_test_matrices({"nsamples": [2, 4, 6, 32], "nbits": [32, 16]})
)
def test_stride_perm(p):
    run_test_vector_sim(
        StridePermutation(p.nsamples, p.nbits),
        stride_perm(p.nsamples, p.nbits),
        cmdline_opts={},
    )
