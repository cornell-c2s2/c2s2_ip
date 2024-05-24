import pytest
from src.tapeins.sp24.tapein2.tests.spi_driver_sim import spi_write
from src.tapeins.sp24.tapein2.interconnect import Interconnect
from src.tapeins.sp24.tapein2.tests.spi_stream_protocol import *
from fixedpt import Fixed, CFixed
from tools.utils import fixed_bits, mk_test_matrices

from src.fft.tests.fft import FFTInterface, FFTPease

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
    in_msgs = [mk_bits(20)(x) for x in in_msgs]
    out_msgs = [mk_bits(20)(x) for x in out_msgs]

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
            spc = retmsg[20]
            print(
                "Trsn" + pad(trsns) + ":",
                valrdy_to_str(in_msgs[in_idx], 1, 1, 6),
                ">",
                valrdy_to_str(retmsg[0:20], retmsg[21], 1, 6),
            )
            if retmsg[21] == 1:
                assert retmsg[0:20] == out_msgs[out_idx]
                out_idx += 1
            in_idx += 1

        else:
            retmsg = spi_write(dut, read_msg())
            print(
                "Trsn" + pad(trsns) + ":",
                valrdy_to_str(0, in_idx < len(in_msgs), spc, 6),
                ">",
                valrdy_to_str(retmsg[0:20], retmsg[21], 1, 6),
            )
            spc = retmsg[20]
            if retmsg[21] == 1:
                assert retmsg[0:20] == out_msgs[out_idx]
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
    SPI_SPI = 0b000  # SPI loopback
    SPI_WSB = 0b001  # SPI to Wishbone
    SPI_FFT = 0b010  # SPI to FFT

    WSB_SPI = 0b100  # Wishbone to SPI
    WSB_FFT = 0b101  # Wishbone to FFT
    WSB_WSB = 0b110  # Wishbone looback


class ClsXbarCfg(int):
    SPI_SPI = 0b0000  # SPI loopback
    SPI_CLS = 0b0001  # SPI to Classifier
    SPI_WSB = 0b0010  # SPI to Wishbone

    WSB_SPI = 0b0100  # Classifier to SPI
    WSB_CLS = 0b0101  # Wishbone to Classifier
    WSB_WSB = 0b0110  # Wishbone loopback

    FFT_SPI = 0b1000  # FFT to SPI
    FFT_CLS = 0b1001  # FFT to Classifier
    FFT_WSB = 0b1010  # FFT to Wishbone


class OutXbarCfg(int):
    SPI_SPI = 0b000  # SPI loopback
    SPI_WSB = 0b001  # SPI to Wishbone

    WSB_SPI = 0b010  # Wishbone to SPI
    WSB_WSB = 0b011  # Wishbone loopback

    CLS_SPI = 0b100  # Classifier to SPI
    CLS_WSB = 0b101  # Classifier to Wishbone


class ClsCfgType(int):
    CTF_FRQ = 6  # Cut-off frequency
    CTF_MAG = 7  # Cut-off Magnitude
    SMP_FRQ = 8  # Sampling Frequency


# Generates classifier config messages
def cls_config_msg(config: ClsCfgType, value: int):
    assert value < 0x10000 and value >= 0
    return (config << 16) | value


# Generates xbar config messages
def input_xbar_config_msg(config: InXbarCfg):
    assert config < 16 and config >= 0
    return 0x10000 | config


# Generates xbar config messages
def cls_xbar_config_msg(config: ClsXbarCfg):
    assert config < 16 and config >= 0
    return 0x30000 | config


# Generates xbar config messages
def output_xbar_config_msg(config: OutXbarCfg):
    assert config < 16 and config >= 0
    return 0x50000 | config


# Generates input/output msgs for inXbar loopback
def loopback_inXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [input_xbar_config_msg(InXbarCfg.SPI_SPI)] + msgs, msgs


# Generates input/output msgs for clsXbar loopback
def loopback_clsXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    new_msgs = [(0x20000 | int(x)) for x in msgs]
    return [cls_xbar_config_msg(ClsXbarCfg.SPI_SPI)] + new_msgs, new_msgs


# Generates input/output msgs for outXbar loopback
def loopback_outXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10
    new_msgs = [(0x40000 | int(x)) for x in msgs]
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
def test_loopback_clsXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = loopback_clsXbar_msg(msgs)
    dut = make_interconnect(cmdline_opts)
    run_interconnect(dut, in_msgs, out_msgs)


@pytest.mark.parametrize(
    "msgs",
    [
        [0x1],
        [0x0],
        [0x1, 0x0],
        [0x0, 0x1],
        [0x1, 0x0, 0x1, 0x0],
        [0x0, 0x1, 0x0, 0x1],
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
        cls_xbar_config_msg(ClsXbarCfg.FFT_SPI),
    ] + [int(x) for x in inputs]

    out_msgs = [(0x20000 | int(x)) for x in outputs]

    return in_msgs, out_msgs


# Generates input/output msgs for classifier from fixedpt inputs/outputs
def classifer_msg(inputs: list[Fixed], outputs: list[int]):

    inputs = [fixed_bits(x) for sample in inputs for x in sample]

    in_msgs = [
        cls_xbar_config_msg(ClsXbarCfg.SPI_CLS),
        output_xbar_config_msg(OutXbarCfg.CLS_SPI),
    ] + [int(x) | 0x20000 for x in inputs]

    out_msgs = [(0x40000 | int(x)) for x in outputs]

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


def test_classifier_manual(cmdline_opts):
    in_msgs, out_msgs = classifer_msg([[fixN(1) for _ in range(32)]], [0x0001])
    dut = make_interconnect(cmdline_opts)
    run_interconnect(dut, in_msgs, out_msgs)


# Composite test that combines loopback and FFT.
def test_compose(cmdline_opts):
    xbar_in_in_msgs, xbar_in_out_msgs = loopback_inXbar_msg([0x5555, 0xAAAA])
    fft_in_msgs, fft_out_msgs = fft_msg(
        [[fixN(1) for _ in range(32)]],
        [[fixN(32)] + [fixN(0) for _ in range(31)]],
    )
    xbar_cls_in_msgs, xbar_cls_out_msgs = loopback_clsXbar_msg([0xAAAA, 0x5555])

    dut = make_interconnect(cmdline_opts)
    num_t1 = run_interconnect(dut, xbar_in_in_msgs, xbar_in_out_msgs, max_trsns=100)
    num_t2 = run_interconnect(dut, fft_in_msgs, fft_out_msgs, curr_trsns=num_t1)
    run_interconnect(dut, xbar_cls_in_msgs, xbar_cls_out_msgs, curr_trsns=num_t2)
