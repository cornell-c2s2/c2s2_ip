import pytest
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from fixedpt import CFixed
from src.fixed_point.combinational.multi_butterfly import (
    MultiButterflyWrapper,
    mk_multi_butterfly_input,
    mk_multi_butterfly_output,
)
from src.fixed_point.utils import mk_butterfly_input, mk_butterfly_output
from src.fixed_point.iterative.tests.complex_multiplier import cmul
import random
from tools.utils import mk_test_matrices
from src.fixed_point.utils import rand_fxp_spec


# Performs the butterfly operation on two complex numbers
# Used to generate the expected output
def butterfly(n, d, a, b, w):
    t = cmul(n, d, b, w)
    return ((a + t).resize(n, d), (a - t).resize(n, d))


# Merge inputs into a single bus
def mk_msg(n, b, aall, ball, wall):
    assert len(aall) == len(ball) == len(wall) == b
    return mk_multi_butterfly_input(n, b)(
        [
            mk_butterfly_input(n)(*a.get(), *b.get(), *w.get())
            for (a, b, w) in zip(aall, ball, wall)
        ]
    )


# Merge outputs into a single bus
def mk_ret(n, b, call, dall):
    assert len(call) == len(dall) == b
    return mk_multi_butterfly_output(n, b)(
        [mk_butterfly_output(n)(*c.get(), *d.get()) for (c, d) in zip(call, dall)]
    )


# Create test parametrization information
# execution_number: number of times to run the test
# sequence_lengths: numbers of inputs to stream through the block
# n: bounds on number of bits in the fixed point number
# d: bounds on number of decimal bits in the fixed point number
# m: optimization parameter
def mk_params(execution_number, sequence_lengths, n, d, m=[0], slow=False):
    if isinstance(n, int):
        n = (n, n)
    if isinstance(d, int):
        d = (d, d)

    res = []

    for k in m:
        for j in range(execution_number):
            for i in sequence_lengths:
                res.append(
                    pytest.param(
                        j,  # execution_number index (unused)
                        i,  # number of inputs to stream
                        n,  # `n` bounds
                        d,  # `d` bounds
                        k,  # optimization parameter
                        id=f"{i} ({n[0]}-{n[1]})-bit, ({d[0]}-{d[1]})-decimal-bit numbers"
                        + (f", {k}-optimized " if k != 0 else ""),
                        marks=pytest.mark.slow if slow else [],
                    )
                )
    return res


# Test harness for streaming data
class TestHarness(Component):
    def construct(s, nbits, ndecimalbits, b):
        s.dut = MultiButterflyWrapper(nbits, ndecimalbits, b)

        s.src = stream.SourceRTL(mk_multi_butterfly_input(nbits))
        s.sink = stream.SinkRTL(mk_multi_butterfly_output(nbits))

        s.src.send //= s.dut.recv
        s.dut.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# return a random fixed point value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "execution_num": list(range(20)),
            "sequence_length": 50,
            "n": (2, 8),
            "d": (0, 8),
            "b": [1, 4, 16],
            "slow": True,
        },
        {
            "execution_num": list(range(10)),
            "sequence_length": 50,
            "n": (16, 32),
            "d": (0, 32),
            "b": [1, 4, 16],
            "slow": True,
        },
        {
            "execution_num": 1,
            "sequence_length": 100,
            "n": [8, 24, 32],
            "d": [0, 8, 16],
            "b": [4, 16],
            "slow": False,
        },
    )
)
def test_random(
    cmdline_opts, p
):  # test individual and sequential multiplications to assure stream system works
    random.seed(random.random() + p.execution_num)
    n, d = rand_fxp_spec(p.n, p.d)

    dat = []
    solns = []

    for i in range(p.sequence_length):
        a = [rand_cfixed(n, d) for _ in range(p.b)]
        b = [rand_cfixed(n, d) for _ in range(p.b)]
        w = [rand_cfixed(n, d) for _ in range(p.b)]

        dat.append(mk_msg(n, p.b, a, b, w))

        c, dd = tuple(
            zip(*[butterfly(n, d, a1, b1, w1) for a1, b1, w1 in zip(a, b, w)])
        )

        solns.append(mk_ret(n, p.b, c, dd))

    model = TestHarness(n, d, p.b)

    model.set_param("top.src.construct", msgs=dat, initial_delay=0, interval_delay=0)

    model.set_param(
        "top.sink.construct",
        msgs=solns,
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": (
                30 + ((n + 2) * 3 + 4) * len(dat)
            ),  # makes sure the time taken grows linearly with respect to n
        },
        duts=["dut.dut"],
    )
