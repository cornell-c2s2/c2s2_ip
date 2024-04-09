import pytest
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim, run_test_vector_sim
from pymtl3.stdlib import stream
from fixedpt import CFixed
from src.fixed_point.combinational.butterfly import Butterfly
from src.fixed_point.sim import butterfly
import random
from tools.utils import mk_packed, mk_list_bitstruct, cfixed_bits
from src.fixed_point.utils import rand_fxp_spec, mk_butterfly_input, mk_butterfly_output


def mk_params(execution_number, sequence_lengths, n, d, bin1, slow=False):
    if isinstance(n, int):
        n = (n, n)
    if isinstance(d, int):
        d = (d, d)

    res = []

    for k in bin1:
        for j in range(execution_number):
            for i in sequence_lengths:
                res.append(
                    pytest.param(
                        j,  # execution_number index (unused)
                        i,  # number of inputs to stream
                        n,  # `n` bounds
                        d,  # `d` bounds
                        k,  # k in one butterfly
                        id=f"{i} ({n[0]}-{n[1]})-bit, ({d[0]}-{d[1]})-decimal-bit numbers"
                        + (f", {k}in1 butterfly "),
                        marks=pytest.mark.slow if slow else [],
                    )
                )
    return res


# return a random fixed point value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )


def gen_random_test_case(n, d, num):
    test_case = [("ar[0] ac[0] br[0] bc[0] wr[0] wc[0] cr[0]* cc[0]* dr[0]* dc[0]* ")]
    for _ in range(num):
        a = rand_cfixed(n, d)
        b = rand_cfixed(n, d)
        w = rand_cfixed(n, d)
        c, dd = butterfly(a, b, w)
        test_case.append(
            [
                a.real.get(),
                a.imag.get(),
                b.real.get(),
                b.imag.get(),
                w.real.get(),
                w.imag.get(),
                c.real.get(),
                c.imag.get(),
                dd.real.get(),
                dd.imag.get(),
            ]
        )
    return test_case


@pytest.mark.parametrize(
    "n, d, a, b, w,",
    [
        (3, 0, (0, 1), (0, 1), (0, 1)),
        (2, 1, (1, 0), (1, 0), (1, 0)),
        (32, 16, (1, 0), (1, 0), (0, 0)),
        (16, 8, (1, 0), (1, 0), (0, 0)),
        (8, 4, (1, 1), (1, 1), (1, 1)),
        (8, 4, (0.5, 0.5), (0.5, 0.5), (1, 0)),
        (6, 3, (3, 3), (3, 3), (1, 0)),  # overflow check
    ],
)
def test_edge(cmdline_opts, n, d, a, b, w):
    a = CFixed(a, n, d)
    b = CFixed(b, n, d)
    w = CFixed(w, n, d)
    c, dd = butterfly(a, b, w)

    model = Butterfly(n, d, 1)

    test_case = [("ar[0] ac[0] br[0] bc[0] wr[0] wc[0] cr[0]* cc[0]* dr[0]* dc[0]* ")]
    test_case.append(
        [
            a.real.get(),
            a.imag.get(),
            b.real.get(),
            b.imag.get(),
            w.real.get(),
            w.imag.get(),
            c.real.get(),
            c.imag.get(),
            dd.real.get(),
            dd.imag.get(),
        ]
    )

    run_test_vector_sim(model, test_case, cmdline_opts)


@pytest.mark.parametrize(
    "sequence_length, n, d",
    [
        (1, 16, 8),
        (50, 16, 8),
        (1, 32, 16),
        (50, 32, 16),
        (1, 64, 32),
        (50, 64, 32),
    ],
)
def test_random(
    cmdline_opts, sequence_length, n, d
):  # test individual and sequential multiplications to assure stream system works

    test_case = gen_random_test_case(n, d, sequence_length)
    model = Butterfly(n, d, 1)

    run_test_vector_sim(model, test_case, cmdline_opts)
