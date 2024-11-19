import pytest
from src.tapeins.sp24.tapein2.test_cocotb.spi_driver_sim import spi_write
from src.tapeins.sp24.tapein2.interconnect2 import Interconnect2
from src.tapeins.sp24.tapein2.test_cocotb.spi_stream_protocol import *
from fixedpt import Fixed, CFixed
from tools.utils import fixed_bits, mk_test_matrices
from src.fft.tests.fft import FFTInterface, FFTPease
from src.classifier.sim import classify
import random

#Pymtl imports (useful helper functions)
from pymtl3.stdlib.stream.ifcs import valrdy_to_str

#Cocotb imports
import cocotb
import os
import sys
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.types.logic_array import *
from cocotb.types.logic import *
from cocotb.runner import get_runner
from cocotb.clock import Clock
from pathlib import Path



# Helper function for interconnect printouts
def pad(n: int) -> str:
    return " " * (3 - len(str(n))) + str(n)


async def run_interconnect(dut, in_msgs, out_msgs, max_trsns=100, curr_trsns=0):
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
            retmsg = await spi_write(dut, write_read_msg(in_msgs[in_idx]))
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
            retmsg = await spi_write(dut, read_msg())
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
    dut = Interconnect2()
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=False))
    dut.sim_reset()
    return dut


class InXbarCfg(int):
    SPI_SPI = 0b0000  # SPI loopback
    SPI_WSB = 0b0001  # SPI to Wishbone
    SPI_FFT = 0b0010  # SPI to FFT

    WSB_SPI = 0b0100  # Wishbone to SPI
    WSB_FFT = 0b0101  # Wishbone to FFT
    WSB_WSB = 0b0110  # Wishbone looback


class ClsXbarCfg(int):
    SPI_SPI = 0b0000  # SPI loopback
    SPI_WSB = 0b0001  # SPI to Wishbone
    SPI_CLS = 0b0010  # SPI to Classifier

    WSB_SPI = 0b0100  # Classifier to SPI
    WSB_WSB = 0b0101  # Wishbone loopback
    WSB_CLS = 0b0110  # Wishbone to Classifier

    FFT_SPI = 0b1000  # FFT to SPI
    FFT_WSB = 0b1001  # FFT to Wishbone
    FFT_CLS = 0b1010  # FFT to Classifier


class OutXbarCfg(int):
    SPI_SPI = 0b0000  # SPI loopback
    SPI_WSB = 0b0001  # SPI to Wishbone

    WSB_SPI = 0b0100  # Wishbone to SPI
    WSB_WSB = 0b0101  # Wishbone loopback

    CLS_SPI = 0b1000  # Classifier to SPI
    CLS_WSB = 0b1001  # Classifier to Wishbone


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

async def reset_dut(dut):
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    await ClockCycles(dut.clk, 1)

@cocotb.test()
async def test_loopback_inXbar(dut):
    in_msgs, out_msgs = loopback_inXbar_msg([0xDEAD, 0xBEEF, 0xCAFE, 0xBABE])
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_interconnect(dut, in_msgs, out_msgs)

@cocotb.test()
async def test_loopback_clsXbar(dut):
    in_msgs, out_msgs = loopback_clsXbar_msg([0xDEAD, 0xBEEF, 0xCAFE, 0xBABE])
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_interconnect(dut, in_msgs, out_msgs)


@cocotb.test()
async def test_loopback_outXbar(dut):
    in_msgs, out_msgs = loopback_outXbar_msg([0x0, 0x1, 0x0, 0x1])
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_interconnect(dut, in_msgs, out_msgs)


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


#@cocotb.test()
async def test_fft_manual(dut):
    in_msgs, out_msgs = fft_msg([[fixN(1) for _ in range(32)]], [[fixN(32)] + [fixN(0) for _ in range(15)]])
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_interconnect(dut, in_msgs, out_msgs)


# Randomized test for the FFT
#@cocotb.test()
async def test_fft_random(dut):
    random.seed(random.random())
    inputs = [
        [
            CFixed((random.uniform(-10, 10), 0), 16, 8)
            for i in range(32)
        ]
        for _ in range(10)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    inputs = [[x.real for x in sample] for sample in inputs]
    outputs = [[x.real for x in sample][:16] for sample in outputs]

    in_msgs, out_msgs = fft_msg(inputs, outputs)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_interconnect(dut, in_msgs, out_msgs, max_trsns=1000)

#@cocotb.test()
async def test_classifier_manual(dut):
    in_msgs, out_msgs = classifer_msg([[fixN(1) for _ in range(16)]], [0x0000])
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_interconnect(dut, in_msgs, out_msgs)


# Composite test that combines loopback and FFT.
#@cocotb.test()
async def test_compose(dut):
    xbar_in_in_msgs, xbar_in_out_msgs = loopback_inXbar_msg([0x5555, 0xAAAA])
    fft_in_msgs, fft_out_msgs = fft_msg(
        [[fixN(1) for _ in range(32)]],
        [[fixN(32)] + [fixN(0) for _ in range(15)]],
    )
    xbar_cls_in_msgs, xbar_cls_out_msgs = loopback_clsXbar_msg([0xAAAA, 0x5555])

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    num_t1 = await run_interconnect(dut, xbar_in_in_msgs, xbar_in_out_msgs, max_trsns=100)
    num_t2 = await run_interconnect(dut, fft_in_msgs, fft_out_msgs, curr_trsns=num_t1)
    await run_interconnect(dut, xbar_cls_in_msgs, xbar_cls_out_msgs, curr_trsns=num_t2)


# Test the FFT -> Classifier pipeline
@cocotb.test()
async def test_fft_classifier_random(dut):
    inputs = [
        [
            CFixed((random.uniform(-10, 10), 0), 16, 8)
            for i in range(32)
        ]
        for _ in range(10)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    fft_inputs = [[x.real for x in sample] for sample in inputs]
    fft_outputs = [[x.real for x in sample][:16] for sample in outputs]

    cutoff_mag = Fixed(0.7, True, 16, 8)

    classifier_outputs = [
        classify(x, 2000, cutoff_mag, 25000) for x in fft_outputs
    ]

    inputs = (
        [  # First, configure the crossbars
            input_xbar_config_msg(InXbarCfg.SPI_FFT),
            cls_xbar_config_msg(ClsXbarCfg.FFT_CLS),
            output_xbar_config_msg(OutXbarCfg.CLS_SPI),
        ]
        + [  # Next, configure the classifier
            cls_config_msg(ClsCfgType.CTF_FRQ, 2000),
            cls_config_msg(ClsCfgType.CTF_MAG, int(cutoff_mag)),
            cls_config_msg(ClsCfgType.SMP_FRQ, 25000),
        ]
        + [  # Finally, send the fft inputs
            int(fixed_bits(x)) for sample in fft_inputs for x in sample
        ]
    )

    outputs = [(0x40000 | int(x)) for x in classifier_outputs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_interconnect(dut, inputs, outputs, max_trsns=1000)
