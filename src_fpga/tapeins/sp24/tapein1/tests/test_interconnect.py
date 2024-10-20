import pytest
from src_fpga.tapeins.sp24.tapein1.tests.spi_driver_sim import spi_write
from src_fpga.tapeins.sp24.tapein1.interconnect import Interconnect
from src_fpga.tapeins.sp24.tapein1.tests.spi_stream_protocol import *
from fixedpt import Fixed, CFixed
from tools.utils import fixed_bits, mk_test_matrices
from src_fpga.fft.tests.fft import FFTInterface, FFTPease
import random
from pymtl3 import *
from pymtl3.stdlib.stream.ifcs import valrdy_to_str
from pymtl3.stdlib.test_utils import (
    mk_test_case_table,
    run_sim,
    config_model_with_cmdline_opts,
)


# Helper function for interconnect printouts
def pad(n: int) -> str:
    return " " * (3 - len(str(n))) + str(n)


def run_interconnect(dut, in_msgs, out_msgs, max_trsns=100, curr_trsns=0):
    """
    Run src/sink testing on the interconnect RTL model, src/sink msgs are
    converted to SPI protocol transactions. Testing is done at the transaction
    level.

    This function can be called multiple times on the same interconnect dut to
    run a composite test which consists of multiple input/output stages.
    E.g. Loopback -> FFT -> Loopback

    Args:
    dut: The interconnect model
    in_msgs: A list of input messages
    out_msgs: A list of expected output messages
    max_trsns: The maximum number of transactions to run
    curr_trsns: The current transaction number
    """
    in_msgs = [mk_bits(18)(x) for x in in_msgs]
    out_msgs = [mk_bits(18)(x) for x in out_msgs]

    in_idx = 0
    out_idx = 0
    trsns = curr_trsns + 1

    spc = 0

    print("")

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"

        if in_idx < len(in_msgs) and spc == 1:
            retmsg = spi_write(dut, write_read_msg(in_msgs[in_idx]))
            spc = retmsg[18]
            print(
                "Trsn" + pad(trsns) + ":",
                valrdy_to_str(in_msgs[in_idx], 1, 1, 6),
                ">",
                valrdy_to_str(retmsg[0:18], retmsg[19], 1, 6),
            )
            if retmsg[19] == 1:
                assert retmsg[0:18] == out_msgs[out_idx]
                out_idx += 1
            in_idx += 1

        else:
            retmsg = spi_write(dut, read_msg())
            print(
                "Trsn" + pad(trsns) + ":",
                valrdy_to_str(0, in_idx < len(in_msgs), spc, 6),
                ">",
                valrdy_to_str(retmsg[0:18], retmsg[19], 1, 6),
            )
            spc = retmsg[18]
            if retmsg[19] == 1:
                assert retmsg[0:18] == out_msgs[out_idx]
                out_idx += 1

        trsns += 1

    return trsns - 1


# Makes a new interconnect dut
def make_interconnect(cmdline_opts):
    dut = Interconnect()
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=False))
    dut.sim_reset()
    return dut


class InXbarCfg(int):
    SPI_SPI = 0b00  # Loopback
    SPI_FFT = 0b01  # FFT


class OutXbarCfg(int):
    SPI_SPI = 0b00  # Loopback
    FFT_SPI = 0b10  # FFT


# Generates xbar config messages
def input_xbar_config_msg(input: InXbarCfg):
    assert input < 4 and input >= 0
    return 0x20000 | input


# Generates xbar config messages
def output_xbar_config_msg(output: OutXbarCfg):
    assert output < 4 and output >= 0
    return 0x30000 | output


# Generates input/output msgs for inXbar loopback
def loopback_inXbar_msg(msgs):
    return [input_xbar_config_msg(InXbarCfg.SPI_SPI)] + msgs, msgs


# Generates input/output msgs for outXbar loopback
def loopback_outXbar_msg(msgs):
    new_msgs = [(0x10000 | int(x)) for x in msgs]
    return [output_xbar_config_msg(OutXbarCfg.SPI_SPI)] + new_msgs, new_msgs


@pytest.mark.parametrize(
    "msgs",
    [
        [0xFFFF],
        [0x0000],
        [0x5555, 0xAAAA],
        [0xAAAA, 0x5555],
        [0xDEAD, 0xBEEF, 0xCAFE, 0xBABE],
        [0xABCD, 0x1234, 0x5678, 0x9ABC, 0xDEF0],
    ],
)
def test_loopback_inXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = loopback_inXbar_msg(msgs)
    dut = make_interconnect(cmdline_opts)
    run_interconnect(dut, in_msgs, out_msgs)


@pytest.mark.parametrize(
    "msgs",
    [
        [0xFFFF],
        [0x0000],
        [0x5555, 0xAAAA],
        [0xAAAA, 0x5555],
        [0xDEAD, 0xBEEF, 0xCAFE, 0xBABE],
        [0xABCD, 0x1234, 0x5678, 0x9ABC, 0xDEF0],
    ],
)
def test_loopback_outXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = loopback_outXbar_msg(msgs)
    dut = make_interconnect(cmdline_opts)
    run_interconnect(dut, in_msgs, out_msgs)


# Generates input/output msgs for FFT from fixedpt inputs/outputs
def fft_msg(inputs: list[Fixed], outputs: list[Fixed]):

    inputs = [fixed_bits(x) for sample in inputs for x in sample]
    outputs = [fixed_bits(x) for sample in outputs for x in sample]

    in_msgs = [
        input_xbar_config_msg(InXbarCfg.SPI_FFT),
        output_xbar_config_msg(OutXbarCfg.FFT_SPI),
    ] + [int(x) for x in inputs]

    out_msgs = [(0x10000 | int(x)) for x in outputs]

    return in_msgs, out_msgs


# Shortcut for creating fixedpt numbers
def fixN(n):
    return Fixed(n, True, 16, 8)


@pytest.mark.parametrize(
    "input, output",
    [
        ([[fixN(1) for _ in range(32)]], [[fixN(32)] + [fixN(0) for _ in range(31)]]),
    ],
)
def test_fft_manual(input, output, cmdline_opts):
    in_msgs, out_msgs = fft_msg(input, output)
    dut = make_interconnect(cmdline_opts)
    run_interconnect(dut, in_msgs, out_msgs)


# Randomized test for the FFT
@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "input_mag": [1, 10],  # Maximum magnitude of the input signal
            "input_num": [1, 10],  # Number of random inputs to generate
            "seed": list(range(2)),  # Random seed
        }
    )
)
def test_fft_random(cmdline_opts, p):
    random.seed(random.random() + p.seed)
    inputs = [
        [
            CFixed((random.uniform(-p.input_mag, p.input_mag), 0), 16, 8)
            for i in range(32)
        ]
        for _ in range(p.input_num)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    inputs = [[x.real for x in sample] for sample in inputs]
    outputs = [[x.real for x in sample] for sample in outputs]

    in_msgs, out_msgs = fft_msg(inputs, outputs)
    dut = make_interconnect(cmdline_opts)
    run_interconnect(dut, in_msgs, out_msgs, max_trsns=1000)


# Composite test that combines loopback and FFT.
def test_compose(cmdline_opts):
    xbar_in_in_msgs, xbar_in_out_msgs = loopback_inXbar_msg([0x5555, 0xAAAA])
    fft_in_msgs, fft_out_msgs = fft_msg(
        [[fixN(1) for _ in range(32)]],
        [[fixN(32)] + [fixN(0) for _ in range(31)]],
    )
    xbar_out_in_msgs, xbar_out_out_msgs = loopback_outXbar_msg([0xAAAA, 0x5555])

    dut = make_interconnect(cmdline_opts)
    num_t1 = run_interconnect(dut, xbar_in_in_msgs, xbar_in_out_msgs, max_trsns=100)
    num_t2 = run_interconnect(dut, fft_in_msgs, fft_out_msgs, curr_trsns=num_t1)
    run_interconnect(dut, xbar_out_in_msgs, xbar_out_out_msgs, curr_trsns=num_t2)
