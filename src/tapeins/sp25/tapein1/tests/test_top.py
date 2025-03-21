"""
This is the cocotb testbench for the Spring 25 top-level.

Most of the testbench was adapted from previous tapeouts.

The tests are laid out in the following order:
1. Loopback tests for
  - spi -> router -> arbiter -> spi
  - spi -> router -> input xbar -> arbiter -> spi
  - spi -> router -> classifier xbar -> arbiter -> spi
  - spi -> router -> output xbar -> arbiter -> spi

Author: Tean Lai
"""
import random
from enum import Enum

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory
from pymtl3 import *
from fixedpt import Fixed, CFixed

from src.tapeins.sp25.tapein1.tests.spi_driver_sim import spi_write_read, spi_write, spi_read
from src.classifier.sim import classify
from tools.utils import fixed_bits
# from src.tapeins.sp25.tapein1.tests.spi_stream_protocol import *
# from tools.utils import fixed_bits

if cocotb.simulator.is_running():
    ADDR_BITS = int(cocotb.top.ADDR_BITS.value)
    DATA_BITS = int(cocotb.top.DATA_BITS.value)
    SPI_PACKET_BITS = int(cocotb.top.SPI_PACKET_BITS.value)


async def run_top(dut, in_msgs: list[int], out_msgs: list[int], max_trsns=30, curr_trsns=0):
    """
    Run src/sink testing. src/snk msgs are converted to SPI protocol transactions.
    Testing is done at the transaction level.

    Args:
    dut: model for top
    in_msgs: a list of input messages
    out_msgs: a list of expected output messages
    max_trsns: the maximum number of transactions to run. test will fail if
      simulations take too long
    curr_trsns: the current transaction number (note from Tean: I've ported this
      over from previous testbenches for now, but I'm thinking of possibly removing it)
    """
    mk = mk_bits(SPI_PACKET_BITS)
    in_msgs = [mk(x) for x in in_msgs]
    out_msgs = [mk(x) for x in out_msgs]

    in_idx = 0
    out_idx = 0
    trsns = curr_trsns + 1

    spc = 0

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"

        dut._log.info("\nnew loop!")
        dut._log.info(f"in_idx is {in_idx}, out_idx is {out_idx}")
        dut._log.info(f"spc = {spc}")
        dut._log.info(f"router_2_clsxbar_val = {dut.Router_to_ClassifierXbar_val.value}")
        dut._log.info(f"router_2_clsxbar_rdy = {dut.Router_to_ClassifierXbar_rdy.value}")


        if in_idx < len(in_msgs) and spc == 1:
            # spi_status, retmsg = await spi_write(dut, write_read_msg(in_msgs[in_idx]))
            spi_status, retmsg = await spi_write_read(dut, in_msgs[in_idx])

            dut._log.info(f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}, sending in {hex(in_msgs[in_idx])}")
            spc = spi_status[0]

            if spi_status[1] == 1:
                assert retmsg == out_msgs[out_idx]
                out_idx += 1
            in_idx += 1

        else:
            # spi_status, retmsg = await spi_write(dut, read_msg())
            spi_status, retmsg = await spi_read(dut)
            dut._log.info(f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}")
            spc = spi_status[0]
            if spi_status[1] == 1:
                assert retmsg == out_msgs[out_idx]
                out_idx += 1

        trsns += 1

    return trsns - 1


@cocotb.test()
async def basic_test(dut):
    """This test just checks if things compile!"""
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 10)
    assert True

class InXbarCfg:
    """
    Represents the message to send to the input crossbar to configure it. For
    example, sending in 0b1111 will configure it to input from router and output
    to arbiter.

    TODO: Need to add rest of config messages. Tean's note: not sure if it might
    be better to have a function to generate the message, since
    """
    ROUTER_ARBITER = 0b1010

class ClsXbarCfg:
    """
    Serves a similar purpose as InXbarCfg, but for the classifier crossbar
    """
    ROUTER_CLS = 0b1001
    ROUTER_ARBITER = 0b1010

class OutXbarCfg:
    """
    Serves a similar purpose as InXbarCfg and ClsXbarCfg, but for the output
    crossbar.
    """
    # ROUTER_ARBITER = 0b110
    CLS_ARBITER = 0b000
    ROUTER_ARBITER = 0b010


class RouterOut:
    """
    The router has several outputs to different blocks. These enums represent
    which output they are to the router.
    """
    LBIST_CTRL             = 0b0000
    IN_XBAR                = 0b0001
    IN_XBAR_CTRL           = 0b0010
    CLS_XBAR               = 0b0011
    CLS_XBAR_CTRL          = 0b0100
    CLS_CUT_FREQ_CTRL      = 0b0101
    CLS_MAG_CTRL           = 0b0110
    OUT_XBAR               = 0b1000
    OUT_XBAR_CTRL          = 0b1001
    ARBITER                = 0b1010


class ArbiterIn:
    """
    The arbiter has several inputs from different blocks. These enums represent
    which input they are to the arbiter.
    """
    ROUTER     = 0
    IN_XBAR    = 1
    CLS_XBAR   = 2
    OUT_XBAR   = 3
    LBIST_CTRL = 4


async def reset_dut(dut):
    """
    Resets dut.
    """
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    await ClockCycles(dut.clk, 3)

def mk_spi_pkt(addr: int, data: int) -> int:
    """Make spi packet. Does bitwise operations to concatenate [addr] and [data]
    together to form a spi packet. The spi packet is equal to {addr, data}."""
    assert not data >> DATA_BITS
    assert not addr >> ADDR_BITS
    return (addr << DATA_BITS) | data

"""
================================================================================
LOOPBACK TESTS
================================================================================
"""

async def test_loopback_noXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> arbiter -> spi.

    We expect the outputs' data to be the same as the inputs', their address
    bits might differ.
    """
    in_msgs = [mk_spi_pkt(RouterOut.ARBITER, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.ROUTER, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_inXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> input xbar -> arbiter -> spi.

    We expect the outputs to be the same as the inputs. We also prepend a
    message to inputs to configure the crossbar.
    """
    config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.IN_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_clsXbar(dut, msgs):
    config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.CLS_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_outXbar(dut, msgs):
    config_msg = mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.OUT_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, msg & 1) for msg in msgs]  # output xbar only takes first bit

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

"""
Generate tests here using test factory to test for different messages, kind of
like with pytest parameters
"""
msgs_values = [
        [0xFFFF],
        [0x0000],
        [0x5555, 0xAAAA],
        [0xAAAA, 0x5555],
        [0xDEAD, 0xBEEF, 0xCAFE, 0xBABE],
        [0xABCD, 0x1234, 0x5678, 0x9ABC, 0xDEF0]
]
# for test in []:
for test in [test_loopback_noXbar, test_loopback_inXbar, test_loopback_clsXbar, test_loopback_outXbar]:
    factory = TestFactory(test)
    factory.add_option("msgs", msgs_values)
    factory.generate_tests()

def fixN(n):
    """Shortcut for creating fixedpt numbers."""
    return Fixed(n, True, 16, 8)

# def gen_fft_msgs(inputs: list[Fixed], outputs: list[Fixed]):
#     """Generates input/output msgs for FFT from fixedpt inputs/outputs."""
#     inputs = [fixed_bits(x) for sample in inputs for x in sample]
#     outputs = [fixed_bits(x) for sample in outputs for x in sample]



@cocotb.test()
async def test_fft_manual(dut, input, output):
    raise NotImplemented

# input_values = [
#     [fixN(1) for _ in range(32)]
# ]

# output_values = [
#     [fixN(32)] + [fixN(0) for _ in range(15)]
# ]

# @cocotb.test()
# async def test_fft_random(dut, input_mag, output_mag):
#     raise NotImplemented

# @cocotb.test()
# async def test_fft_to_classifier_random(
#         dut, input_mag, input_num, cutoff_freq, cutoff_mag, sampling_freq):
#     raise NotImplemented


"""
================================================================================
CLASSIFIER TESTS
================================================================================
"""
def classifier_msg(inputs: list[Fixed], outputs: list[int]):

    inputs = [int(fixed_bits(x)) for sample in inputs for x in sample]
    assert all(type(x) == int for x in inputs)

    in_msgs = [
        mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_CLS),
        mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.CLS_ARBITER)
    ] + [mk_spi_pkt(RouterOut.CLS_XBAR, x) for x in inputs]

    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, x) for x in outputs]

    return in_msgs, out_msgs


@cocotb.test()
async def test_classifier_manual(dut):
    # in_msgs, out_msgs = classifier_msgj
    # in_msgs, out_msgs = [], []
    in_msgs, out_msgs = classifier_msg([[fixN(1) for _ in range(16)]], [0x0000])
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)
