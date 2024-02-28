from src.fft.helpers.crossbar import Crossbar
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3 import mk_bits, Bits1
import pytest
import math
import random
from tools.utils import mk_test_matrices, cfixed_bits, fixed_bits
from fixedpt import Fixed, CFixed


# front crossbar (set FRONT = 1 in verilog model)
# def crossbar_front(n_samples: int, stage_fft: int, cbar_in: list[any]) -> list[any]:
#     cbar_out = [None for _ in range(n_samples)]

#     for m in range(0, 2**stage_fft):
#         for i in range(m, n_samples, 2 ** (stage_fft + 1)):
#             cbar_out[i + m] = cbar_in[i]
#             cbar_out[i + m + 1] = cbar_in[i + 2**stage_fft]

#     return cbar_out


# the two bools are recv_val and send_rdy
def crossbar_front(
    n_samples: int, stage_fft: int, cbar_in: list[tuple[any, bool, bool]]
) -> list[tuple[any, bool, bool]]:
    cbar_out = [None for _ in range(n_samples)]
    recv_rdy = [None for _ in range(n_samples)]
    send_val = [None for _ in range(n_samples)]

    for m in range(2**stage_fft):
        for i in range(m, n_samples, 2 ** (stage_fft + 1)):
            cbar_out[i + m] = cbar_in[i][0]
            cbar_out[i + m + 1] = cbar_in[i + 2**stage_fft][0]

            recv_rdy[i + m] = cbar_in[i][2]
            recv_rdy[i + m + 1] = cbar_in[i + 2**stage_fft][2]

            send_val[i + m] = cbar_in[i][1]
            send_val[i + m + 1] = cbar_in[i + 2**stage_fft][1]

    print("recv_rdy: " + str(recv_rdy))
    print("send_val: " + str(send_val))
    print([(a, b, c) for a, b, c in zip(cbar_out, recv_rdy, send_val)])
    return [(a, b, c) for a, b, c in zip(cbar_out, recv_rdy, send_val)]


# back crossbar (set FRONT = 0 in verilog model)
def crossbar_back(n_samples: int, stage_fft: int, cbar_in: list[any]) -> list[any]:
    cbar_out = [None for _ in range(n_samples)]

    for m in range(0, 2**stage_fft):
        for i in range(m, n_samples, 2 ** (stage_fft + 1)):
            cbar_out[i] = cbar_in[i + m]
            cbar_out[i + 2**stage_fft] = cbar_in[i + m + 1]

    return cbar_out


# get output of crossbar_front
# def gen_crossbar_front(n_samples, stage_fft, cbar_in: list[tuple[CFixed, bool, bool]]):
#     # print(n_samples)
#     return [
#         (
#             " ".join([f"recv_real[{i}] recv_imaginary[{i}]" for i in range(n_samples)])
#             + " ".join([f"recv_val[{i}] recv_rdy[{i}]*" for i in range(n_samples)])
#             + " ".join(
#                 [f"send_real[{i}]* send_imaginary[{i}]*" for i in range(n_samples)]
#             )
#             + " ".join([f"send_val[{i}]*" for i in range(n_samples)])
#             + " ".join([f"send_rdy[{i}]" for i in range(n_samples)])
#         ),
#         sum(  # recv real and imaginary
#             [
#                 list(
#                     cfixed_bits(x[0])
#                 )  # Returns a tuple here so we unpack it to a list and take the sum
#                 for x in cbar_in
#             ],
#             [],
#         )
#         + sum(  # recv val and recv rdy
#             [[Bits1(int(x[1])), Bits1(int(x[2]))] for x in cbar_in],
#             [],
#         )
#         + sum(  # send real and imaginary
#             [
#                 list(
#                     cfixed_bits(x)
#                 )  # Returns a tuple here so we unpack it to a list and take the sum
#                 for x in crossbar_front(n_samples, stage_fft, [c[0] for c in cbar_in])
#             ],
#             [],
#         )
#         + [
#             Bits1(int(x))
#             for x in crossbar_front(n_samples, stage_fft, [c[1] for c in cbar_in])
#         ]  # send val
#         + [
#             Bits1(int(x))
#             for x in crossbar_front(n_samples, stage_fft, [c[2] for c in cbar_in])
#         ],  # send rdy
#     ]


def gen_crossbar_front(n_samples, stage_fft, cbar_in: list[tuple[CFixed, bool, bool]]):
    print(cbar_in)
    print(Bits1(int(x[1])) for x in cbar_in)
    # print(n_samples)
    return [
        (
            " ".join([f"recv_real[{i}] recv_imaginary[{i}]" for i in range(n_samples)])
            + " ".join([f"recv_val[{i}]" for i in range(n_samples)])
            + " ".join([f"recv_rdy[{i}]*" for i in range(n_samples)])
            + " ".join(
                [f"send_real[{i}]* send_imaginary[{i}]*" for i in range(n_samples)]
            )
            + " ".join([f"send_val[{i}]*" for i in range(n_samples)])
            + " ".join([f"send_rdy[{i}]" for i in range(n_samples)])
        ),
        sum(  # recv real and imaginary
            [
                list(
                    cfixed_bits(x[0])
                )  # Returns a tuple here so we unpack it to a list and take the sum
                for x in cbar_in
            ],
            [],
        )
        + [Bits1(int(x[1])) for x in cbar_in]  # recv val
        + [
            Bits1(int(x[1])) for x in crossbar_front(n_samples, stage_fft, cbar_in)
        ]  # recv rdy
        + sum(  # send real and imaginary
            [
                list(
                    cfixed_bits(x[0])
                )  # Returns a tuple here so we unpack it to a list and take the sum
                for x in crossbar_front(n_samples, stage_fft, cbar_in)
            ],
            [],
        )
        + [
            Bits1(int(x[2])) for x in crossbar_front(n_samples, stage_fft, cbar_in)
        ]  # send val
        + [Bits1(int(x[2])) for x in cbar_in],  # send rdy
    ]


# get output of crossbar_back
# def gen_crossbar_back(n_samples, stage_fft, cbar_in: list[tuple[CFixed, bool, bool]]):
#     # print(n_samples)
#     return [
#         (
#             " ".join([f"recv_real[{i}] recv_imaginary[{i}]" for i in range(n_samples)])
#             + " ".join([f"recv_val[{i}] recv_rdy[{i}]*" for i in range(n_samples)])
#             + " ".join(
#                 [f"send_real[{i}]* send_imaginary[{i}]*" for i in range(n_samples)]
#             )
#             + " ".join([f"send_val[{i}]*" for i in range(n_samples)])
#             + " ".join([f"send_rdy[{i}]" for i in range(n_samples)])
#         ),
#         sum(  # recv real and imaginary
#             [
#                 list(
#                     cfixed_bits(x[0])
#                 )  # Returns a tuple here so we unpack it to a list and take the sum
#                 for x in cbar_in
#             ],
#             [],
#         )
#         + sum(  # recv val and recv rdy
#             [[Bits1(int(x[1])), Bits1(int(x[2]))] for x in cbar_in],
#             [],
#         )
#         + sum(  # send real and imaginary
#             [
#                 list(
#                     cfixed_bits(x)
#                 )  # Returns a tuple here so we unpack it to a list and take the sum
#                 for x in crossbar_back(n_samples, stage_fft, [c[0] for c in cbar_in])
#             ],
#             [],
#         )
#         + [
#             Bits1(int(x))
#             for x in crossbar_back(n_samples, stage_fft, [c[1] for c in cbar_in])
#         ]  # send val
#         + [
#             Bits1(int(x))
#             for x in crossbar_back(n_samples, stage_fft, [c[2] for c in cbar_in])
#         ],  # send rdy
#     ]


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
            True,
            True
            # random.choice([True, False]),
            # random.choice([True, False]),
        )
        for _ in range(n_samples)
    ]


# @pytest.mark.parametrize(
#     *mk_test_matrices(
#         {
#             "fp_spec": [(32, 16), (32, 31), (32, 24)],
#             "n_samples": [8, 32, 256, 512],
#         }
#     )
# )
@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16)],
            "n_samples": [8],
        }
    )
)
# def test_front(cmdline_opts, p):
#     for stage in range(0, int(math.log2(p.n_samples))):
#         run_test_vector_sim(
#             Crossbar(p.fp_spec[0], p.n_samples, stage, 1),
#             gen_crossbar_front(p.n_samples, stage, gen_input(*p.fp_spec, p.n_samples)),
#             cmdline_opts,
#         )


def test_front(cmdline_opts, p):
    stage = 0
    run_test_vector_sim(
        Crossbar(p.fp_spec[0], p.n_samples, stage, 1),
        gen_crossbar_front(p.n_samples, stage, gen_input(*p.fp_spec, p.n_samples)),
        cmdline_opts,
    )


# @pytest.mark.parametrize(
#     *mk_test_matrices(
#         {
#             "fp_spec": [(32, 16), (32, 31), (32, 24)],
#             "n_samples": [8, 32, 256, 512],
#         }
#     )
# )
# def test_back(cmdline_opts, p):
#     for stage in range(0, int(math.log2(p.n_samples))):
#         run_test_vector_sim(
#             Crossbar(p.fp_spec[0], p.n_samples, stage, 0),,
#             gen_crossbar_back(p.n_samples, stage, gen_input(*p.fp_spec, p.n_samples)),
#             cmdline_opts,
#         )
