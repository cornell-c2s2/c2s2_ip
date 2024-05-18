import pytest
from pymtl3.stdlib.test_utils import run_test_vector_sim
import random
from src.fixed_point.combinational.multiplier import Multiplier
from fixedpt import Fixed
from src.fixed_point.utils import mk_params, rand_fxp_spec
from src.fixed_point.sim import multiply


# Get a random fixed point number
def rand_fixed(n, d):
    return Fixed(random.randint(0, (1 << n) - 1), 1, n, d, raw=True)


# Creates `num` random test cases
def gen_random_test_case(n, d, num):
    test_cases = [("a b c* ")]
    for _ in range(num):
        a = rand_fixed(n, d)
        b = rand_fixed(n, d)
        c = multiply(a, b)
        test_cases.append([a.get(), b.get(), c.get()])
    return test_cases


# Merge a and b into a larger number
def mk_msg(n, a, b):
    return (a << n) | b


@pytest.mark.parametrize(
    "n, d, a, b",
    [
        (3, 0, 3, 3),  # overflow check
        (2, 1, 0.5, -0.5),
        (6, 3, -4, -0.125),  # 100.000 * 111.111 = 000.100
        (6, 3, 3.875, -0.125),  # -0.375
        [32, 16, 1, 1],
    ],
)
def test_edge(cmdline_opts, n, d, a, b):
    a = Fixed(a, 1, n, d)
    b = Fixed(b, 1, n, d)
    c = multiply(a, b)

    test_case = [("a b c* ")]
    test_case.append([a.get(), b.get(), c.get()])

    run_test_vector_sim(Multiplier(n, d, 1), test_case, cmdline_opts)


@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d",
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(20, [100], (16, 64), (0, 64), slow=True) +
    # Extensively tests numbers with certain important bit sizes.
    sum(
        [
            mk_params(1, [100], n, d, slow=True)
            for (n, d) in [(8, 4), (24, 8), (32, 24), (32, 16), (64, 32), (32, 0)]
        ],
        [],
    ),
)
def test_random(cmdline_opts, execution_number, sequence_length, n, d):
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)
    run_test_vector_sim(
        Multiplier(n, d, 1),
        gen_random_test_case(n, d, sequence_length),
        cmdline_opts,
    )
