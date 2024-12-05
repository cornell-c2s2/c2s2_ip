import pytest
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from fixedpt import CFixed
from src.fixed_point.combinational.complex_multiplier import ComplexMultiplierWrapper
import random
from src.fixed_point.utils import (
    mk_params,
    rand_fxp_spec,
    mk_complex_multiplier_input,
    mk_complex_multiplier_output,
)
from src.fixed_point.sim import complex_multiply


# Merge a and b into a larger number
def mk_msg(n, a, b):
    return mk_complex_multiplier_input(n)(*a, *b)


def mk_ret(n, c):
    return mk_complex_multiplier_output(n)(*c)


# Test harness for streaming data
class TestHarness(Component):
    def construct(s, n, d, num_mults=3):
        s.dut = ComplexMultiplierWrapper(n, d, num_mults)

        s.src = stream.SourceRTL(mk_complex_multiplier_input(n))
        s.sink = stream.SinkRTL(mk_complex_multiplier_output(n))

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


# return a random fxp value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )


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

    model = TestHarness(n, d)

    model.set_param(
        "top.src.construct",
        msgs=[mk_msg(n, a.get(), b.get())],
        initial_delay=0,
        interval_delay=0,
    )

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, complex_multiply(a, b).get())],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(model, cmdline_opts, duts=["dut.dut"])


@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d",
    # Runs tests on smaller number sizes
    mk_params(20, [1, 50], (2, 8), (0, 8), slow=True) +
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(10, [1, 50], (16, 64), (0, 64), slow=True) +
    # Extensively tests numbers with certain important bit sizes.
    sum(
        [
            mk_params(1, [100], n, d, slow=True)
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
def test_random_1mult(cmdline_opts, execution_number, sequence_length, n, d):
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)
    dat = [(rand_cfixed(n, d), rand_cfixed(n, d)) for i in range(sequence_length)]
    solns = [complex_multiply(*i) for i in dat]
    print(
        "Testing",
        [(i[0].bin(dot=True), i[1].bin(dot=True)) for i in dat],
        [i.bin(dot=True) for i in solns],
    )

    model = TestHarness(n, d, num_mults=1)

    dat = [mk_msg(n, i[0].get(), i[1].get()) for i in dat]

    model.set_param("top.src.construct", msgs=dat, initial_delay=0, interval_delay=0)

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, c.get()) for c in solns],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": (
                30 + (3 * (n + 2) + 2) * len(dat)
            ),  # makes sure the time taken grows linearly with respect to 3n
        },
        duts=["dut.dut"],
    )


@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d",
    # Runs tests on smaller number sizes
    mk_params(20, [1, 50], (2, 8), (0, 8), slow=True) +
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(10, [1, 50], (16, 64), (0, 64), slow=True) +
    # Extensively tests numbers with certain important bit sizes.
    sum(
        [
            mk_params(1, [100], n, d, slow=True)
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
def test_random_3mult(cmdline_opts, execution_number, sequence_length, n, d):
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)
    dat = [(rand_cfixed(n, d), rand_cfixed(n, d)) for i in range(sequence_length)]
    solns = [complex_multiply(i[0], i[1]) for i in dat]
    print(
        "Testing",
        [(i[0].bin(dot=True), i[1].bin(dot=True)) for i in dat],
        [i.bin(dot=True) for i in solns],
    )

    model = TestHarness(n, d, num_mults=3)

    dat = [mk_msg(n, i[0].get(), i[1].get()) for i in dat]

    model.set_param("top.src.construct", msgs=dat, initial_delay=0, interval_delay=0)

    model.set_param(
        "top.sink.construct",
        msgs=[mk_ret(n, c.get()) for c in solns],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": (
                30 + (3 * (n + 2) + 2) * len(dat)
            ),  # makes sure the time taken grows linearly with respect to 3n
        },
        duts=["dut.dut"],
    )
