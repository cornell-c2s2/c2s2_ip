import pytest
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from fixedpt import CFixed
from src.fixed_point.combinational.harnesses.complex_multiplier import (
    ComplexMultiplierTestHarness,
)
import random
from src.fixed_point.tools.params import mk_params, rand_fxp_spec


# Complex multiplication with fixed precision
def cmul(n, d, a, b):
    ac = (a.real * b.real).resize(None, n, d)
    bc = (a.imag * b.imag).resize(None, n, d)

    c = (
        (a.real + a.imag).resize(None, n, d) * (b.real + b.imag).resize(None, n, d)
    ).resize(None, n, d)

    return CFixed.cast((ac - bc, c - ac - bc)).resize(n, d)


# Merge a and b into a larger number
def mk_msg(n, a, b):
    return (a[0] << 3 * n) | (a[1] << 2 * n) | (b[0] << n) | b[1]


def mk_ret(n, c):
    return (c[0] << n) | c[1]


# Test harness for streaming data
class Harness(Component):
    def construct(s, mult, n):
        s.mult = mult

        s.src = stream.SourceRTL(mk_bits(4 * n))

        s.sink = stream.SinkRTL(mk_bits(2 * n))

        s.src.send //= s.mult.recv
        s.mult.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

    def line_trace(s):
        return (
            s.src.line_trace()
            + " > "
            + s.mult.line_trace()
            + " > "
            + s.sink.line_trace()
        )


# return a random fxp value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )


# Initialize a simulatable model
def create_model(n, d):
    model = ComplexMultiplierTestHarness(n, d)

    return Harness(model, n)


@pytest.mark.parametrize(
    "n, d, a, b",
    [
        (3, 0, (0, 1), (0, 1)),  # i * i = -1
        (2, 1, (1, 0), (1, 0)),  # 1 * 1 = 1
        (8, 4, (1, 1), (1, 1)),
        (8, 4, (0.5, 0.5), (0.5, 0.5)),
        (6, 3, (3, 3), (3, 3)),  # overflow check
    ],
)
def test_edge(n, d, a, b, cmdline_opts):
    a = CFixed(a, n, d)
    b = CFixed(b, n, d)

    model = create_model(n, d)

    model.set_param(
        "top.src.construct",
        msgs=[mk_msg(n, a.get(), b.get())],
        initial_delay=0,
        interval_delay=0,
    )

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, cmul(n, d, a, b).get())],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={"max_cycles": None, **cmdline_opts},
    )


@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d",
    # Runs tests on smaller number sizes
    mk_params(50, [1, 50], (2, 8), (0, 8), slow=True) +
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(20, [1, 10, 50, 100], (16, 64), (0, 64), slow=True) +
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
def test_random(execution_number, sequence_length, n, d):
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)
    dat = [(rand_cfixed(n, d), rand_cfixed(n, d)) for i in range(sequence_length)]
    solns = [cmul(n, d, i[0], i[1]) for i in dat]
    print(
        "Testing",
        [(i[0].bin(dot=True), i[1].bin(dot=True)) for i in dat],
        [i.bin(dot=True) for i in solns],
    )

    model = create_model(n, d)

    dat = [mk_msg(n, i[0].get(), i[1].get()) for i in dat]

    model.set_param("top.src.construct", msgs=dat, initial_delay=5, interval_delay=5)

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, c.get()) for c in solns],
        initial_delay=5,
        interval_delay=5,
    )

    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            # "dump_vcd": f"rand_{execution_number}_{sequence_length}_{n}_{d}",
            "dump_vcd": False,
            "max_cycles": (
                30 + (3 * (n + 2) + 2) * len(dat)
            ),  # makes sure the time taken grows linearly with respect to 3n
        },
    )
