import pytest
from src.tapeins.sp24.tapein1.tests.spi_driver_sim import spi_write
from src.tapeins.sp24.tapein1.interconnect import Interconnect
from src.tapeins.sp24.tapein1.tests.spi_stream_protocol import *
from fixedpt import Fixed, CFixed
from tools.utils import fixed_bits

# from src.fft.tests.fft import *

from pymtl3 import *
from pymtl3.stdlib.test_utils import (
    mk_test_case_table,
    run_sim,
    config_model_with_cmdline_opts,
)

max_trsns = 100


def run_interconnect(in_msgs, out_msgs, cmdline_opts):
    dut = Interconnect()
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=False))
    dut.sim_reset()

    in_msgs = [mk_bits(18)(x) for x in in_msgs]
    out_msgs = [mk_bits(18)(x) for x in out_msgs]

    in_idx = 0
    out_idx = 0
    trsns = 0

    spc = 0

    print("\nBEGIN TEST\n=============================")

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"

        if in_idx < len(in_msgs) and spc == 1:
            retmsg = spi_write(dut, write_read_msg(in_msgs[in_idx]))
            print("Trsn ", trsns, " SENT: ", in_msgs[in_idx])
            in_idx += 1
            spc = retmsg[18]
            if retmsg[19] == 1:
                assert retmsg[0:18] == out_msgs[out_idx]
                out_idx += 1
                print("Trsn ", trsns, " RECV: ", retmsg[0:18])

        else:
            retmsg = spi_write(dut, read_msg())
            spc = retmsg[18]
            if retmsg[19] == 1:
                assert retmsg[0:18] == out_msgs[out_idx]
                out_idx += 1
                print("Trsn ", trsns, " RECV: ", retmsg[0:18])

        trsns += 1


class InXbarCfg(int):
    SPI_SPI = 0b00  # Loopback
    SPI_FFT = 0b01  # FFT


class OutXbarCfg(int):
    SPI_SPI = 0b00  # Loopback
    FFT_SPI = 0b10  # FFT


def input_xbar_config_msg(input: InXbarCfg):
    assert input < 4 and input >= 0
    return 0x20000 | input


def output_xbar_config_msg(output: OutXbarCfg):
    assert output < 4 and output >= 0
    return 0x30000 | output


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
    # make sure all messages are 16 bits
    for msg in msgs:
        assert msg < 0x10000 and msg >= 0
    in_msgs = [input_xbar_config_msg(InXbarCfg.SPI_SPI)] + msgs
    out_msgs = msgs
    run_interconnect(in_msgs, out_msgs, cmdline_opts)


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
    for msg in msgs:
        assert msg < 0x10000 and msg >= 0
    in_msgs = [
        output_xbar_config_msg(OutXbarCfg.SPI_SPI),
    ] + msgs
    out_msgs = msgs
    run_interconnect(in_msgs, out_msgs, cmdline_opts)


def run_fft(inputs: list[Fixed], outputs: list[Fixed], cmdline_opts):

    inputs = [fixed_bits(x) for sample in inputs for x in sample]
    outputs = [fixed_bits(x) for sample in outputs for x in sample]

    in_msgs = [
        input_xbar_config_msg(InXbarCfg.SPI_FFT),
        output_xbar_config_msg(OutXbarCfg.FFT_SPI),
    ] + [int(x) for x in inputs]

    out_msgs = [(0x10000 | int(x)) for x in outputs]

    run_interconnect(in_msgs, out_msgs, cmdline_opts)


def fixN(n):
    return Fixed(n, True, 16, 8)


@pytest.mark.parametrize(
    "input, output",
    [
        ([[fixN(1) for _ in range(32)]], [[fixN(32)] + [fixN(0) for _ in range(31)]]),
    ],
)
def test_fft_manual(input, output, cmdline_opts):
    print(fixN(1))
    run_fft(input, output, cmdline_opts)
