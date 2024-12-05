from src.fft.cooley_tukey.helpers.crossbar import Crossbar
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3 import mk_bits, Bits1
import pytest
import math
import random
from tools.utils import mk_test_matrices, cfixed_bits, fixed_bits
from fixedpt import Fixed, CFixed
from src.fft.cooley_tukey.sim import crossbar


# the two bools are recv_val and send_rdy
def crossbar_front(
    n_samples: int, stage_fft: int, cbar_in: list[tuple[any, bool, bool]]
) -> list[tuple[any, bool, bool]]:
    cbar_in, send_rdy, recv_val = map(list, zip(*cbar_in))

    cbar_out = crossbar(n_samples, stage_fft, cbar_in, True)
    recv_rdy = crossbar(n_samples, stage_fft, send_rdy, True)
    send_val = crossbar(n_samples, stage_fft, recv_val, True)
    return list(zip(cbar_out, recv_rdy, send_val))


# back crossbar (set FRONT = 0 in verilog model)
def crossbar_back(
    n_samples: int, stage_fft: int, cbar_in: list[tuple[any, bool, bool]]
) -> list[tuple[any, bool, bool]]:
    cbar_in, send_rdy, recv_val = map(list, zip(*cbar_in))

    cbar_out = crossbar(n_samples, stage_fft, cbar_in, False)
    recv_rdy = crossbar(n_samples, stage_fft, send_rdy, False)
    send_val = crossbar(n_samples, stage_fft, recv_val, False)
    return list(zip(cbar_out, recv_rdy, send_val))


# Generate a test vector for the crossbar
def gen_crossbar_test(
    n_samples: int,
    stage_fft: int,
    cbar_in: list[tuple[CFixed, bool, bool]],
    front: bool,
):
    crossbar_fn = crossbar_front if front else crossbar_back

    output = crossbar_fn(n_samples, stage_fft, cbar_in)

    send_msg, recv_rdy, send_val = zip(*output)

    recv_msg, send_rdy, recv_val = zip(*cbar_in)

    recv_msg = sum(map(list, map(cfixed_bits, recv_msg)), [])
    recv_val = list(map(Bits1, recv_val))
    send_rdy = list(map(Bits1, send_rdy))

    send_msg = sum(map(list, map(cfixed_bits, send_msg)), [])
    send_val = list(map(Bits1, send_val))
    recv_rdy = list(map(Bits1, recv_rdy))

    return [
        (
            " ".join(
                [f"recv_real[{i}] recv_imaginary[{i}]" for i in range(n_samples)]
                + [f"recv_val[{i}]" for i in range(n_samples)]
                + [f"recv_rdy[{i}]*" for i in range(n_samples)]
                + [f"send_real[{i}]* send_imaginary[{i}]*" for i in range(n_samples)]
                + [f"send_val[{i}]*" for i in range(n_samples)]
                + [f"send_rdy[{i}]" for i in range(n_samples)]
            )
        ),
        recv_msg + recv_val + recv_rdy + send_msg + send_val + send_rdy,
    ]


# generate a random CFixed value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )


# generate a list of random CFixed values and random recv_val and send_rdy signals
def gen_input(
    bit_width: int, decimal_pt: int, n_samples: int
) -> list[tuple[CFixed, bool, bool]]:
    return [
        (
            rand_cfixed(bit_width, decimal_pt),
            random.choice([True, False]),
            random.choice([True, False]),
        )
        for i in range(n_samples)
    ]


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(8, 0)],
            "n_samples": [2, 8, 32],
            "front": [True, False],
        },
        {
            "fp_spec": [(4, 0)],
            "n_samples": [512],
            "front": [True, False],
            "slow": True,
        },
    )
)
def test_crossbar(cmdline_opts, p):
    for stage in range(0, int(math.log2(p.n_samples))):
        run_test_vector_sim(
            Crossbar(p.fp_spec[0], p.n_samples, stage, int(p.front)),
            gen_crossbar_test(
                p.n_samples, stage, gen_input(*p.fp_spec, p.n_samples), p.front
            ),
            cmdline_opts,
        )
