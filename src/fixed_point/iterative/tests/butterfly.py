import pytest
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from fixedpt import CFixed
from src.fixed_point.iterative.harnesses.butterfly import (
    Butterfly,
    mk_butterfly_input,
    mk_butterfly_output,
)
from src.fixed_point.iterative.tests.complex_multiplier import cmul
import random
from tools.utils import mk_packed
from src.fixed_point.tools.params import rand_fxp_spec


# Performs the butterfly operation on two complex numbers
# Used to generate the expected output
def butterfly(n, d, a, b, w):
    t = cmul(n, d, b, w)
    return ((a + t).resize(n, d), (a - t).resize(n, d))


# Merge inputs into a single bus
def mk_msg(n, a, b, w):
    return mk_packed(n)(*a, *b, *w)


# Merge outputs into a single bus
def mk_ret(n, c, d):
    return mk_packed(n)(*c, *d)


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
    def construct(s, nbits, ndecimalbits, m=0):
        s.mult = Butterfly(nbits, ndecimalbits, m)

        s.src = stream.SourceRTL(mk_butterfly_input(nbits))

        s.sink = stream.SinkRTL(mk_butterfly_output(nbits))

        s.src.send //= s.mult.recv
        s.mult.send //= s.sink.recv

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
    "n, d, a, b, w,",
    [
        (3, 0, (0, 1), (0, 1), (0, 1)),
        (2, 1, (1, 0), (1, 0), (1, 0)),
        (8, 4, (1, 1), (1, 1), (1, 1)),
        (8, 4, (0.5, 0.5), (0.5, 0.5), (1, 0)),
        (6, 3, (3, 3), (3, 3), (1, 0)),  # overflow check
    ],
)
def test_edge(cmdline_opts, n, d, a, b, w):
    a = CFixed(a, n, d)
    b = CFixed(b, n, d)
    w = CFixed(w, n, d)

    model = TestHarness(n, d)

    model.set_param(
        "top.src.construct",
        msgs=[mk_msg(n, a.get(), b.get(), w.get())],
        initial_delay=0,
        interval_delay=0,
    )

    (c, d) = butterfly(n, d, a, b, w)

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, c.get(), d.get())],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts,
        duts=["mult"],
    )


@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d, m",
    # Runs tests on smaller number sizes
    mk_params(50, [1, 50], (2, 8), (0, 8), slow=True) +
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(20, [1, 100], (16, 64), (0, 64), slow=True) +
    # Extensively tests numbers with certain important bit sizes.
    sum(
        [
            [
                *mk_params(1, [20], n, d, slow=False),
                *mk_params(1, [1000], n, d, slow=True),
            ]
            for (n, d) in [
                (8, 4),
                (24, 8),
                (32, 24),
                (32, 16),
                (64, 32),
            ]
        ],
        [],
    ),
)
def test_random(
    cmdline_opts, execution_number, sequence_length, n, d, m
):  # test individual and sequential multiplications to assure stream system works
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)
    assert m == 0

    dat = [
        (rand_cfixed(n, d), rand_cfixed(n, d), rand_cfixed(n, d))
        for i in range(sequence_length)
    ]
    solns = [butterfly(n, d, i[0], i[1], i[2]) for i in dat]

    model = TestHarness(n, d)

    dat = [mk_msg(n, i[0].get(), i[1].get(), i[2].get()) for i in dat]

    model.set_param("top.src.construct", msgs=dat, initial_delay=0, interval_delay=0)

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, c.get(), d.get()) for (c, d) in solns],
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
        duts=["mult"],
    )


@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d, m",
    # Runs tests on smaller number sizes
    mk_params(50, [1, 50], (2, 8), (0, 8), m=range(1, 5), slow=True) +
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(20, [1, 100], (16, 64), (0, 64), m=range(1, 5), slow=True) +
    # Extensively tests numbers with certain important bit sizes.
    # Uses
    sum(
        [
            [
                *mk_params(1, [20], n, d, m=range(1, 5), slow=False),
                *mk_params(1, [1000], n, d, m=range(1, 5), slow=True),
            ]
            for (n, d) in [
                (8, 4),
                (24, 8),
                (32, 24),
                (32, 16),
                (64, 32),
            ]
        ],
        [],
    ),
)
def test_optimizations(
    cmdline_opts, execution_number, sequence_length, n, d, m
):  # test modules without multiplication
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)
    opt_omega = [CFixed(i, n, d) for i in [(1, 0), (-1, 0), (0, 1), (0, -1)]]

    dat = [
        (rand_cfixed(n, d), rand_cfixed(n, d), rand_cfixed(n, d))
        for _ in range(sequence_length)
    ]
    solns = [butterfly(n, d, i[0], i[1], opt_omega[m - 1]) for i in dat]

    model = TestHarness(n, d, m)

    dat = [mk_msg(n, i[0].get(), i[1].get(), i[2].get()) for i in dat]

    model.set_param("top.src.construct", msgs=dat, initial_delay=5, interval_delay=5)

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, c.get(), d.get()) for (c, d) in solns],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": (
                30 + 6 * len(dat)
            ),  # makes sure the time taken grows constantly
        },
        duts=["mult"],
    )
