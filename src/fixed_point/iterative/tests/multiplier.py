import pytest

from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from fixedpt import Fixed

from src.fixed_point.iterative.multiplier import MultiplierWrapper
from src.fixed_point.utils import (
    mk_multiplier_input,
    mk_multiplier_output,
)
import random
from src.fixed_point.utils import mk_params, rand_fxp_spec
from src.fixed_point.sim import multiply


# Test harness for streaming data
class TestHarness(Component):
    def construct(s, n, d):
        s.dut = MultiplierWrapper(n, d)

        s.src = stream.SourceRTL(mk_multiplier_input(n))
        s.sink = stream.SinkRTL(mk_multiplier_output(n))

        s.src.send //= s.dut.recv
        s.dut.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# return a random fxp value
def rand_fixed(n, d):
    return Fixed(random.randint(0, (1 << n) - 1), 1, n, d, raw=True)


@pytest.mark.parametrize(
    "n, d, a, b",
    [
        (3, 0, 3, 3),  # overflow check
        (2, 1, 0.5, -0.5),
        (6, 3, -4, -0.125),  # 100.000 * 111.111 = 000.100
        (6, 3, 3.875, -0.125),  # -0.375
    ],
)
def test_edge(cmdline_opts, n, d, a, b):
    a = Fixed(a, 1, n, d)
    b = Fixed(b, 1, n, d)

    model = TestHarness(n, d)

    model.set_param(
        "top.src.construct",
        msgs=[mk_multiplier_input(n)(a.get(), b.get())],
        initial_delay=0,
        interval_delay=0,
    )

    model.set_param(
        "top.sink.construct",
        msgs=[mk_multiplier_output(n)(multiply(a, b).get())],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts,
        duts=["dut.dut"],
    )


# Test individual and sequential multiplications to assure stream system works
# Generates random data to stream through the multiplier with random bit width information
@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d",
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(20, [100], (16, 64), (0, 64), slow=True) +
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
def test_random(cmdline_opts, execution_number, sequence_length, n, d):
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)
    dat = [
        {"a": rand_fixed(n, d), "b": rand_fixed(n, d)} for i in range(sequence_length)
    ]
    solns = [multiply(i["a"], i["b"]) for i in dat]

    model = TestHarness(n, d)

    dat = [mk_multiplier_input(n)(i["a"].get(), i["b"].get()) for i in dat]

    model.set_param("top.src.construct", msgs=dat, initial_delay=5, interval_delay=5)

    model.set_param(
        "top.sink.construct",
        msgs=[mk_multiplier_output(n)(c.get()) for c in solns],
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": (
                30 + (n + 2) * len(dat)
            ),  # makes sure the time taken grows linearly with respect to n
        },
        duts=["dut.dut"],
    )
