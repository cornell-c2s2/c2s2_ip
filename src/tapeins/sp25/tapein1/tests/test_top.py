"""
This is the cocotb testbench for the Spring 25 top-level.

Most of the testbench was adapted from previous tapeouts.

The tests are laid out in the following order:
1. Loopback tests for
  - spi -> router -> arbiter -> spi
  - spi -> router -> input xbar -> arbiter -> spi
  - spi -> router -> classifier xbar -> arbiter -> spi
  - spi -> router -> output xbar -> arbiter -> spi
2. FFT tests
3. Classifier tests
4. FFT -> Classifier tests

The tests are intended to be run with the run_tests script located in the tools/
directory. This script parallelizes the tests, otherwise running all the tests 
at once would take a long time.

When writing tests, you can follow this general framework:
- Figure out what the intended inputs and outputs are for the test
- Configure the crossbars and any other necessary components
  - InXbarCfg, ClsXbarCfg, and OutXbarCfg are useful for this
  - Make sure to prepend the configuration messages to the input messages
- Convert the inputs into SPI packets using the correct address bits with mk_addr_bits
  - RouterOut is useful for this
- Convert the outputs into SPI packets using the correct address bits
  - ArbiterIn is useful for this
- Run the test using the run_top function, which takes care of sending the
  inputs and checking the outputs
- Note: you generally shouldn't need to interact with the DUT directly, as the
  run_top function handles that for you

Since we are using cocotb with Makefiles, we can use the TestFactory to generate 
tests for different input values. This is similar to how pytest parameters work.

Author: Tean Lai, Akshati Vaishnav
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
from src.classifier.sim import classify, frequency_bins
from src.classifier.tests_cocotb.classifier_model import classify
from src.fft.tests.fft import FFTInterface, FFTPease
from tools.utils import fixed_bits

random.seed("C2S2")

if cocotb.simulator.is_running():
    ADDR_BITS = int(cocotb.top.ADDR_BITS.value)
    DATA_BITS = int(cocotb.top.DATA_BITS.value)
    SPI_PACKET_BITS = int(cocotb.top.SPI_PACKET_BITS.value)
    # CLASSIFIER_SAMPLES = int(cocotb.top.classifier.CLASSIFER_SAMPLES.value)

async def run_top(
    dut,
    in_msgs: list[int],
    out_msgs: list[int],
    max_trsns=30,
    curr_trsns=0,
    use_spi=1,
    num_config=0,
):
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
    # SPI messages
    dut._log.info(f"in_msgs = {in_msgs}")
    dut._log.info(f"out_msgs = {out_msgs}")
    mk = mk_bits(SPI_PACKET_BITS)
    config_msgs = []
    in_msgs_fifo = []
    if use_spi:
        in_msgs = [mk(x) for x in in_msgs]
        out_msgs = [mk(x) for x in out_msgs]
    else:
        mk_fifo_config = mk_bits(8)
        config_msgs = [mk(x) for x in in_msgs[:num_config]]
        in_msgs_fifo = [mk_fifo_config(x) for x in in_msgs[num_config:]]
    dut._log.info(f"config_msgs = {config_msgs}")
    dut._log.info(f"in_msgs_fifo = {in_msgs_fifo}")
    in_idx = 0
    out_idx = 0
    trsns = curr_trsns + 1

    spc = 0

    # FIFO messages
    fifo_in = [int(x) for x in in_msgs_fifo]
    fifo_out = [int(x) for x in out_msgs]
    hex_fifo_in = [hex(i) for i in fifo_in]
    dut._log.info(f"fifo_in = {hex_fifo_in}")

    # access FIFO submodule
    fifo = dut.async_fifo
    fifo_config_done = 0

    hex_fifo_out = [hex(i) for i in fifo_out]
    dut._log.info(f"fifo_out = {hex_fifo_out}")
    dut._log.info(f"use_spi = {use_spi}")

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"

        # The following logging statements are for debugging purposes. Feel free
        # to modify them as needed.
        dut._log.info("\nnew loop!")
        dut._log.info(
            f"in_idx is {in_idx}, out_idx is {out_idx}, len(fifo_in): {len(fifo_in)}"
        )
        dut._log.info(f"spc = {spc}")
        dut._log.info(
            f"router_2_clsxbar_val = {dut.Router_to_ClassifierXbar_val.value}"
        )
        dut._log.info(
            f"router_2_clsxbar_rdy = {dut.Router_to_ClassifierXbar_rdy.value}"
        )

        # use SPI to send and receive data
        if use_spi:
            if in_idx < len(in_msgs) and spc == 1:
                spi_status, retmsg = await spi_write_read(dut, in_msgs[in_idx])

                dut._log.info(
                    f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}, sending in {hex(in_msgs[in_idx])}"
                )
                spc = spi_status[0]

                if spi_status[1] == 1:
                    assert retmsg == out_msgs[out_idx]
                    out_idx += 1
                in_idx += 1

            else:
                spi_status, retmsg = await spi_read(dut)
                dut._log.info(f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}")
                spc = spi_status[0]
                if spi_status[1] == 1:
                    assert retmsg == out_msgs[out_idx]
                    out_idx += 1

        # use ASYNC FIFO to sent input data, router to send configuration messages, arbiter to receive messages
        else:

            # send in the SPI configuration messages for the path (only need to do this once!)
            if not fifo_config_done:
                # reset FIFO to 0
                fifo.async_rst.value = 0
                await ClockCycles(dut.clk, 1)

                for config_idx in range(len(config_msgs)):
                    spi_status, retmsg = await spi_write(dut, config_msgs[config_idx])
                    dut._log.info(
                        f"[CONFIG] Sent {hex(config_msgs[config_idx])}, got {hex(retmsg)}"
                    )

                # reset FIFO to 1
                fifo.async_rst.value = 1
                await ClockCycles(dut.clk, 1)

                # reset FIFO to 0
                fifo.async_rst.value = 0

                # This needs to be 4 cycles to allow for values to change in the reg file
                await ClockCycles(dut.clk, 4)
                dut._log.info(f"[SPI CONFIG] Completed!")

                # only need to configure once
                fifo_config_done = 1

            # Send input FIFO msg if ready and haven't already sent current msg
            if fifo.istream_rdy.value == 1 and in_idx < len(fifo_in):
                dut._log.info(f"[FIFO TX] Sending msg: {hex(fifo_in[in_idx] & 0xFF)}")
                fifo.istream_msg.value = fifo_in[in_idx] & 0xFF
                fifo.istream_val.value = 1
                await ClockCycles(dut.ext_clk, 2)
                in_idx += 1
                fifo.istream_val.value = 0
            else:
                await ClockCycles(dut.clk, 1)

            # wait for output from router
            spi_status, retmsg = await spi_read(dut)
            output_msg = mk(retmsg)
            dut._log.info(f"SPI retmsg: {hex(output_msg)}")

            spc = spi_status[0]

            # if SPI minion is valid
            if spi_status[1] == 1:
                assert (
                    output_msg == out_msgs[out_idx]
                ), f"Output mismatch: got {hex(int(output_msg))}, expected {hex(int(out_msgs[out_idx]))}"
                dut._log.info("[FIFO] Correct FIFO output message!")
                out_idx += 1

        trsns += 1

    return trsns - 1


@cocotb.test()
async def basic_test(dut):
    """This test just checks if things compile!"""
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 10)
    assert True

# @cocotb.test()
# async def print_test(dut):
#     "this test is simply for print debugging purposes"
#     cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
#     await ClockCycles(dut.clk, 10)
#     dut._log.info(f"{dut.classifier.BIT_WIDTH.value}")
#     dut._log.info(f"{dut.classifier.DECIMAL_PT.value}")
#     dut._log.info(f"{dut.classifier.N_SAMPLES.value}")

class InXbarCfg:
    """
    Represents the message to send to the input crossbar to configure it. For
    example, sending in 0b1010 will configure it to input from router and output
    to arbiter.

    TODO: Need to add rest of config messages. Tean's note: not sure if it might
    be better to have a function to generate the message, since
    """
    ROUTER_ARBITER = 0b1010
    ROUTER_FFT1 = 0b1000
    ROUTER_FFT2 = 0b1001
    LFSR_FFT1 = 0b0000
    LFSR_FFT2 = 0b0001
    FIFO_ARBITER = 0b0110
    FIFO_FFT1 = 0b0100
    FIFO_FFT2 = 0b0101

class ClsXbarCfg:
    """
    Serves a similar purpose as InXbarCfg, but for the classifier crossbar
    """
    ROUTER_CLS     = 0b1001
    ROUTER_ARBITER = 0b1010
    FFT1_ARBITER   = 0b0010
    FFT2_ARBITER   = 0b0110
    FFT1_CLS       = 0b0001
    FFT2_CLS       = 0b0101
    FFT1_MISR      = 0b0000
    FFT2_MISR      = 0b0100

class OutXbarCfg:
    """
    Serves a similar purpose as InXbarCfg and ClsXbarCfg, but for the output
    crossbar.

    This should correspond with the Output  addressing scheme in the RTL.
    """
    CLS_ARBITER    = 0b000
    ROUTER_ARBITER = 0b010


class RouterOut:
    """
    The router has several outputs to different blocks. These enums represent
    which output they are to the router. This is intended to be used as the 
    address bits for the SPI packet sent to the router. 

    This should correspond with the Router addressing scheme in the RTL.
    """
    LBIST_CTRL             = 0b0000
    IN_XBAR                = 0b0001
    IN_XBAR_CTRL           = 0b0010
    CLS_XBAR               = 0b0011
    CLS_XBAR_CTRL          = 0b0100
    CLS_CUT_FREQ_CTRL      = 0b0101
    CLS_MAG_CTRL           = 0b0110
    CLS_SAMP_FREQ_CTRL     = 0b0111
    OUT_XBAR               = 0b1000
    OUT_XBAR_CTRL          = 0b1001
    ARBITER                = 0b1010


class ArbiterIn:
    """
    The arbiter has several inputs from different blocks. These enums represent
    which input they are to the arbiter. This is intended to be used as the
    address bits for the SPI packet sent to the arbiter.

    This should correspond with the Arbiter addressing scheme in the RTL.
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

    We expect the outputs' data to be the same as the inputs', their address bits
    might differ. We also prepend a message to inputs to configure the crossbar.
    """
    config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.IN_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_clsXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> classifier xbar -> arbiter -> spi.

    We expect the outputs' data to be the same as the inputs', their address
    bits might differ. We also prepend a message to inputs to configure the crossbar.
    """
    config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.CLS_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_outXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> output xbar -> arbiter -> spi.

    We DON'T expect the outputs' data to be the same as the inputs'. We only 
    extract the least significant bit from the message since the output crossbar
    has an output bitwidth of 1. As usual, we also prepend a message to inputs to 
    configure the crossbar.
    """
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
    # for test in [test_loopback_noXbar, test_loopback_outXbar]:
    factory = TestFactory(test)
    factory.add_option("msgs", msgs_values)
    factory.generate_tests()

"""
FIFO LOOPBACK TEST
"""


async def test_fifo_loopback_inXbar(dut, msgs):
    """
    Tests loopback route: fifo -> packager -> input xbar -> arbiter -> spi.

    the input address is still configured by making SPI packets and setting ctrl bits through router
    since that's the only way of setting them.
    """
    config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.FIFO_ARBITER)

    in_msgs = [config_msg] + [msg for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, (msg << 8)) for msg in msgs]

    cocotb.start_soon(Clock(dut.ext_clk, 2, "ns").start())  # input clk
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())  # output clk
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, use_spi=0, num_config=1, max_trsns=32)


"""
Generate tests here using test factory to test for different messages, kind of
like with pytest parameters
"""
# FIFO only takes in 8-bit messages
fifo_msgs_values = [
    [0xFF, 0xFF],
    [0x00, 0x00],
    [0x55, 0x55, 0xAA, 0xAA],
    [0xAA, 0xAA, 0x55, 0x55],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xAB],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE],
]

for test in [test_fifo_loopback_inXbar]:
    factory = TestFactory(test)
    factory.add_option("msgs", fifo_msgs_values)
    factory.generate_tests()


"""
================================================================================
FFT TESTS
Tests for:
- spi -> router -> input xbar -> fft -> classifier xbar -> arbiter -> spi
================================================================================
"""
def fixN(n):
    """Shortcut for creating fixed-point numbers."""
    return Fixed(n, True, 16, 8)


def fixN_fifo(n):
    """Shortcut for creating fixed-point numbers."""
    return Fixed(n, True, 8, 0)


def fft_msg(inputs: list[Fixed], outputs: list[Fixed], fft_num, config=True):
    """Generate SPI packets for FFT input/output from fixed-point numbers."""

    assert fft_num in [1, 2]
    
    #ensure that input and output samples are converted from fixed to bits
    inputs = [fixed_bits(sample) for sample in inputs]
    outputs = [fixed_bits(sample) for sample in outputs]

    #configure input and output crossbars to send messages to/receive messages from FFT2
    if fft_num == 1:
        in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1)
        out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_ARBITER)
    else:
        in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT2)
        out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_ARBITER)
    
    # send fft inputs to router and fft outputs to Arbiter from XBar
    in_msgs = [mk_spi_pkt(RouterOut.IN_XBAR, int(x)) for x in inputs]
    out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, int(x)) for x in outputs]

    #complete input and output message configurations
    if config:
        in_msgs = [in_xbar_config_msg, out_xbar_config_msg] + in_msgs
    
    return in_msgs, out_msgs

def fft_fifo_msg(dut, inputs: list[Fixed], outputs: list[Fixed], fft_num):
    """Generate SPI packets for FFT input/output from fixed-point numbers."""

    # ensure that input and output samples are converted from fixed to bits
    inputs = [fixed_bits(sample) for sample in inputs[0]]
    outputs = [fixed_bits(sample) for sample in outputs[0]]

    # configure input and output crossbars to send messages to/receive messages from FFT1
    if fft_num == 1:
        in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.FIFO_FFT1)
        out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_ARBITER)
    else:
        in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.FIFO_FFT2)
        out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_ARBITER)

    # send fft inputs to router and fft outputs to Arbiter from XBar
    fft_input_msgs = [x for x in inputs]
    fft_output_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, int(x)) for x in outputs]

    # complete input and output message configurations
    in_msgs = [in_xbar_config_msg, out_xbar_config_msg] + fft_input_msgs
    out_msgs = fft_output_msgs
    dut._log.info(f"in_msgs: {in_msgs}")

    return in_msgs, out_msgs

def flatten_list(lst):
    return [item for sub in lst for item in sub]

def test_fft_random_msg(dut, fft_num):
    random.seed(0xfeedbaba)
    input_mag = 2 ** 31
    input_num = 50

    inputs = [
        [
            CFixed((random.uniform(-2 ** 32, 2 ** 31 - 1), 0), 16, 8)
            for i in range(32)
        ]
        for _ in range(input_num)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    fft_inputs = []
    fft_outputs = []
    count = 0
    for _ in range(input_num):
        # while count < input_num:
        inputs = [
            CFixed((random.uniform(-input_mag, input_mag), 0), 16, 8)
            for i in range(32)
        ]
        # inputs = [[x.real for x in sample] for sample in inputs]
        outputs = model.transform(inputs)

        inputs = [x.real for x in inputs]
        outputs = [x.real for x in outputs][:16]
        outputs = [int(x.bin(), 2) for x in outputs]
        # dut._log.info(f"outputs: {[int(x.bin(), 2) for x in outputs]}")

        # outputs = [[x.real for x in sample][:16] for sample in outputs]
        # for o in outputs:
        #     if int(o) >> 16:
        #         break
        # else:

        fft_inputs.extend(inputs)
        fft_outputs.extend(outputs)
        count += 1
        # dut._log.info(f"We have {count} tests")

    # dut._log.info(f"We have {count} tests")

    assert count > 0

    # dut._log.info(f"{type(fft_inputs[0])}")
    # dut._log.info(f"{type(fft_outputs[0])}")

    if fft_num == 1:
        inputs = (
            [  # First, configure the crossbars
                mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1),
                mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_ARBITER),
            ]
            + [  # Finally, send the fft inputs
                mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for x in fft_inputs
                # int(fixed_bits(x)) for sample in fft_inputs for x in sample
            ]
        )
    else:
        inputs = (
            [  # First, configure the crossbars
                mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT2),
                mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_ARBITER),
            ]
            + [  # Finally, send the fft inputs
                mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for x in fft_inputs
                # int(fixed_bits(x)) for sample in fft_inputs for x in sample
            ]
        )

    # some random irrelevant message we can add for some delays
    # dummy = mk_spi_pkt(RouterOut.OUT_XBAR, OutXbarCfg.CLS_ARBITER)
    # for x in fft_inputs:
    #     inputs.append(mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))))
    #     for _ in range(random.randint(0, 3)):
    #         inputs.append(dummy)

    outputs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, int(x)) for x in fft_outputs]

    return inputs, outputs
    # cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    # await reset_dut(dut)
    # await run_top(dut, inputs, outputs, max_trsns=3000)

"""
-----------
FFT1 TESTS
-----------
"""
async def test_fft1_manual(dut, input_output):
    inputs, outputs = input_output
    in_msgs, out_msgs = fft_msg(inputs, outputs, 1)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=100)

async def test_fft1_manual_fifo(dut, input, output):
    """
    Tests loopback route: fifo -> packager -> input xbar -> fft1 -> cls xbar -> arbiter -> spi.

    the input address is still configured by making SPI packets and setting ctrl bits through router
    since that's the only way of setting them.
    """
    # input, output = input_output
    in_msgs, out_msgs = fft_fifo_msg(dut, input, output, 1)

    cocotb.start_soon(Clock(dut.ext_clk, 2, "ns").start())
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=150, use_spi=0, num_config=2)

@cocotb.test()
async def test_fft1_random(dut):
    # input, output = input_output
    in_msgs, out_msgs = test_fft_random_msg(dut, 1)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=3000)

"""
-----------
FFT2 TESTS
-----------
"""
async def test_fft2_manual(dut, input_output):
    inputs, outputs = input_output
    in_msgs, out_msgs = fft_msg(inputs, outputs, 2)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=100)

async def test_fft2_manual_fifo(dut, input, output):
    """
    Tests loopback route: fifo -> packager -> input xbar -> fft1 -> cls xbar -> arbiter -> spi.

    the input address is still configured by making SPI packets and setting ctrl bits through router
    since that's the only way of setting them.
    """
    in_msgs, out_msgs = fft_fifo_msg(dut, input, output, 2)

    cocotb.start_soon(Clock(dut.ext_clk, 2, "ns").start())
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=150, use_spi=0, num_config=2)

@cocotb.test()
async def test_fft2_random(dut):
    # input, output = input_output
    in_msgs, out_msgs = test_fft_random_msg(dut, 2)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=3000)

"""
-----------
Alternating FFT tests
-----------
"""
def gen_periodic(magnitude, period, n_samples):
    """
    Idea is:
    gen_periodic(4, 2, 8) would make [4, 0, 4, 0, 4, 0, 4, 0]
    gen_periodic(2, 1, 4) would make [2, 2, 2, 2]
    gen_periodic(1, 4, 4) would make [1, 0, 0, 0]
    """
    return [fixN(magnitude if x % period == 0 else 0) for x in range(n_samples)]

# Test Data
fft_io_values = [
    # ([[fixN(1) for _ in range(32)]], [[fixN(32)] + [fixN(0) for _ in range(15)]]),
    # ([[fixN(1 if x % 2 == 0 else 0) for x in range(32)]], [[fixN(1 if x % 16 == 0 else 0) for x in range(32)]]),
    # ([[fixN(1)] + [fixN(0) for _ in range(31)]], [[fixN(1) for _ in range(16)]]),

    (gen_periodic(1, 1, 32), gen_periodic(32, 32, 16)),  # 1, 1, 1, 1, ... -> 32, 0, 0, 0, ...
    (gen_periodic(1, 1, 32) + gen_periodic(1, 1, 32), gen_periodic(32, 32, 16) + gen_periodic(32, 32, 16)),  # 1, 1, 1, 1, ... -> 32, 0, 0, 0, ...
    (gen_periodic(1, 2, 32), gen_periodic(16, 16, 16)),  # 1, 0, 1, 0, ... -> 16, 0, 0, 0, 0, 0
    (gen_periodic(1, 4, 32), gen_periodic(8, 8, 16)),    # 1, 0, 0, 0, 1, 0, 0, 0, ... -> 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, ....
    (gen_periodic(1, 8, 32), gen_periodic(4, 4, 16)),    
    (gen_periodic(1, 16, 32), gen_periodic(2, 2, 16)),    
    (gen_periodic(1, 32, 32), gen_periodic(1, 1, 16)),   # 1, 0, 0, 0, ... -> 1, 1, 1, 1, ...
]


def gen_periodic_fifo(magnitude, period, n_samples):
    """
    Idea is:
    gen_periodic(4, 2, 8) would make [4, 0, 4, 0, 4, 0, 4, 0]
    gen_periodic(2, 1, 4) would make [2, 2, 2, 2]
    gen_periodic(1, 4, 4) would make [1, 0, 0, 0]
    """
    return [fixN_fifo(magnitude if x % period == 0 else 0) for x in range(n_samples)]


# Test Data
fft_io_values_fifo = [
    # ([[fixN(1) for _ in range(32)]], [[fixN(32)] + [fixN(0) for _ in range(15)]]),
    # ([[fixN(1 if x % 2 == 0 else 0) for x in range(32)]], [[fixN(1 if x % 16 == 0 else 0) for x in range(32)]]),
    # ([[fixN(1)] + [fixN(0) for _ in range(31)]], [[fixN(1) for _ in range(16)]]),
    (
        gen_periodic_fifo(1, 1, 32),
        gen_periodic_fifo(32, 32, 16),
    ),  # 1, 1, 1, 1, ... -> 32, 0, 0, 0, ...
    (
        gen_periodic_fifo(1, 1, 32) + gen_periodic_fifo(1, 1, 32),
        gen_periodic_fifo(32, 32, 16) + gen_periodic_fifo(32, 32, 16),
    ),  # 1, 1, 1, 1, ... -> 32, 0, 0, 0, ...
    (
        gen_periodic_fifo(1, 2, 32),
        gen_periodic_fifo(16, 16, 16),
    ),  # 1, 0, 1, 0, ... -> 16, 0, 0, 0, 0, 0
    (
        gen_periodic_fifo(1, 4, 32),
        gen_periodic_fifo(8, 8, 16),
    ),  # 1, 0, 0, 0, 1, 0, 0, 0, ... -> 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, ....
    (gen_periodic_fifo(1, 8, 32), gen_periodic_fifo(4, 4, 16)),
    (gen_periodic_fifo(1, 16, 32), gen_periodic_fifo(2, 2, 16)),
    (
        gen_periodic_fifo(1, 32, 32),
        gen_periodic_fifo(1, 1, 16),
    ),  # 1, 0, 0, 0, ... -> 1, 1, 1, 1, ...
]
# @cocotb.test
async def test_fft_alternation(dut):
    """
    This test might be useless for the current version. 
    The idea is send some to fft1 and then send some to fft2. The problem is you
    can't send inputs to fft1 while fft2 is not done sending outputs and vice 
    versa.
    """

    random.seed(0xfeedbaba)

    iterations = 2
    in_msgs = []
    out_msgs = []

    # assert len(inputs) == len(outputs)
    current_fft = None
    for i in range(iterations):
        new_fft = random.randint(1, 2)

        config = False
        if current_fft != new_fft:
            config = True
            current_fft = new_fft

        # test_in, test_out = fft_io_values[i % len(fft_io_values)]
        test_in, test_out = fft_io_values[0]
        # dut._log.info(f"test_in = {len(test_in)}, test_out = {len(test_out)}")
        # dut._log.info(f"sending to fft {current_fft}")
        test_in, test_out = fft_msg(test_in, test_out, current_fft, config=True)
        in_msgs.extend(test_in)
        out_msgs.extend(test_out)

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=600)


"""
-----------
RUN FFT TESTS
-----------
"""


# Test Data
# inputs are 8 bits, lower 0 bits are fractional
fifo_input_values = [[[fixN_fifo(1) for _ in range(32)]]]

fifo_output_values = [[[fixN(32)] + [fixN(0) for _ in range(15)]]]

# Register test factory
# for test in [test_fft1_manual, test_fft2_manual, test_fft_alternation]:
for test in [test_fft1_manual, test_fft2_manual]:
    factory = TestFactory(test)
    factory.add_option("input_output", fft_io_values)
    # factory.add_option("output", output_values)
    factory.generate_tests()

for test in [test_fft1_manual_fifo, test_fft2_manual_fifo]:
    factory = TestFactory(test)
    # factory.add_option("input_output", fft_io_values_fifo)
    factory.add_option("input", fifo_input_values)
    factory.add_option("output", fifo_output_values)
    factory.generate_tests()

"""
================================================================================
CLASSIFIER TESTS
================================================================================
"""
def classifier_msg(inputs: list[Fixed], outputs: list[int], config_xbars=True):
    """
    Generate SPI packets for classifier input/output from fixed-point numbers.

    Args
    - inputs: A list of lists of fixed-point numbers representing the input samples.
    - outputs: A list of integers representing the expected output samples.

    Returns a tuple of two lists:
    - The first list contains the input messages to be sent
    - The second list contains the output messages to be received
    """

    inputs = [int(fixed_bits(x)) for sample in inputs for x in sample]
    assert all(type(x) == int for x in inputs)

    in_msgs = [mk_spi_pkt(RouterOut.CLS_XBAR, x) for x in inputs]

    if config_xbars:
        in_msgs = [
            mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_CLS),
            mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.CLS_ARBITER)
        ] + in_msgs

    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, x) for x in outputs]

    return in_msgs, out_msgs

@cocotb.test()
async def test_classifier_manual(dut):
    in_msgs, out_msgs = classifier_msg([[fixN(1) for _ in range(16)]], [0x0000])
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

@cocotb.test()
async def test_classifier_random(dut):
    in_msgs = []
    out_msgs = []

    # inputs, outputs = classifier_msg([[fixN(random.uniform(-10, 10)) for _ in range(16)]])

    cocotb.start_soon(Clock(dut.ck, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)


async def test_classifier_manual2(dut, fp_spec, sampling_freq, cutoff_mag, cutoff_freq):
    # n_samples = CLASSIFIER_SAMPLES
    n_samples = 16
    # assert False, "check we can use 16"

    # freq_bins = frequency_bins()
    freq_bins = frequency_bins(sampling_freq, n_samples)
    cutoff_i = None
    for i, freq in enumerate(freq_bins):
        if freq > cutoff_freq:
            cutoff_i = i
            break

    if cutoff_i is None:
        above_cutoff_input = [
            Fixed(cutoff_mag * random.uniform(-2, 2), 1, *fp_spec)
            for _ in range(n_samples)
        ]

        above_cutoff_expected = 0
        check(above_cutoff_input, above_cutoff_expected)
    else:
        above_cutoff_input = [
            Fixed(cutoff_mag * random.uniform(-1, 1), 1, *fp_spec)
            for _ in range(n_samples)
        ]

        above_cutoff_input[random.randint(cutoff_i, n_samples - 1)] = Fixed(
            cutoff_mag * random.uniform(1, 2) * random.choice([-1, 1]), 1, *fp_spec
        )
        above_cutoff_expected = 1

        check(above_cutoff_input, above_cutoff_expected)

        below_cutoff_input = [
            Fixed(cutoff_mag * random.uniform(-1, 1), 1, *fp_spec)
            for _ in range(n_samples)
        ]

        # below_cutoff_input[random.randint(0, cutoff_i - 1)] = Fixed(

        # )


test_matrix = {
    # "n_samples": [4, 16, 32],
    "fp_spec": [
        (16, 8),
        (32, 16),
    ],
    "sampling_freq": [44100, 44800],
    "cutoff_mag": [0.33, 1, 63.32],
    "cutoff_freq": [0, 1000, 1400, 10000],
}
factory = TestFactory(test_classifier_manual2)
for k in test_matrix:
    factory.add_option(k, test_matrix[k])


"""
================================================================================
FFT -> CLASSIFIER TESTS
Tests for:
- spi -> router -> input xbar -> fft -> classifier xbar -> classifier -> output xbar -> arbiter -> spi
================================================================================
"""
async def test_fft_classifier_random(dut, input_mag, input_num, cutoff_freq, cutoff_mag, sampling_freq):
    random.seed(0xfeedbaba)

    inputs = [
        [
            CFixed((random.uniform(-input_mag, input_mag), 0), 16, 8)
            for i in range(32)
        ]
        for _ in range(input_num)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    fft_inputs = [[x.real for x in sample] for sample in inputs]
    fft_outputs = [[x.real for x in sample][:16] for sample in outputs]

    cutoff_mag = Fixed(cutoff_mag, True, 16, 8)

    classifier_outputs = [
        classify(x, cutoff_freq, cutoff_mag, sampling_freq) for x in fft_outputs
    ]

    inputs = (
        [  # First, configure the crossbars
            mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1),
            mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_CLS),
            mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.CLS_ARBITER),
        ]
        + [  # Next, configure the classifier
            mk_spi_pkt(RouterOut.CLS_CUT_FREQ_CTRL, cutoff_freq),
            mk_spi_pkt(RouterOut.CLS_MAG_CTRL, int(cutoff_mag)),
            mk_spi_pkt(RouterOut.CLS_SAMP_FREQ_CTRL, sampling_freq),
        ]
        + [  # Finally, send the fft inputs
            mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for sample in fft_inputs for x in sample
            # int(fixed_bits(x)) for sample in fft_inputs for x in sample
        ]
    )

    outputs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, x) for x in classifier_outputs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, inputs, outputs, max_trsns=1000)


async def test_fft_classifier_random_fifo(
    dut, input_mag, input_num, cutoff_freq, cutoff_mag, sampling_freq
):
    random.seed(0xFEEDBABA)

    inputs = [
        [CFixed((random.uniform(-input_mag, input_mag), 0), 16, 8) for i in range(32)]
        for _ in range(input_num)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    fft_inputs = [[x.real for x in sample] for sample in inputs]
    fft_outputs = [[x.real for x in sample][:16] for sample in outputs]

    cutoff_mag = Fixed(cutoff_mag, True, 16, 8)

    classifier_outputs = [
        classify(x, cutoff_freq, cutoff_mag, sampling_freq) for x in fft_outputs
    ]

    inputs = (
        [  # First, configure the crossbars
            mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.FIFO_FFT1),
            mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_CLS),
            mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.CLS_ARBITER),
        ]
        + [  # Next, configure the classifier
            mk_spi_pkt(RouterOut.CLS_CUT_FREQ_CTRL, cutoff_freq),
            mk_spi_pkt(RouterOut.CLS_MAG_CTRL, int(cutoff_mag)),
            mk_spi_pkt(RouterOut.CLS_SAMP_FREQ_CTRL, sampling_freq),
        ]
        + [  # Finally, send the fft inputs, split into two 8-bit chunks
            byte
            for sample in fft_inputs
            for x in sample
            for byte in [
                (int(fixed_bits(x)) >> 8) & 0xFF,
                int(fixed_bits(x)) & 0xFF,
            ]  # MSB, LSB
        ]
    )

    outputs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, x) for x in classifier_outputs]

    cocotb.start_soon(Clock(dut.ext_clk, 2, "ns").start())
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, inputs, outputs, max_trsns=1000, use_spi=0, num_config=6)


# input_mag_values = [1, 10, 2**30]
input_mag_values = [1, 10]
# input_num_values = [1, 10]
# input_num_values = [10]
input_num_values = [1]
# generic = [0x0000, 0xFFFF, 0x5555,  0xAAAA]
# generic = [0x0000, 0xFFFF]
# cutoff_freq_values = [0, 1000, 1400, 2000, 10000, 0xffff]
cutoff_freq_values = [0, 1000, 1400, 2000, 10000]
# cutoff_freq_values = [0, 1000, 2000, 10000]
# cutoff_freq_values = [0, 1000, 10000]
# cutoff_mag_values = [0.33, 0.7, 1, 2.3, 63.32]
cutoff_mag_values = [0.33, 1, 63.32]
# sampling_freq_values = [44800, 44100, 25000]
sampling_freq_values = [44800, 25000, 0xffff]


for test in [test_fft_classifier_random, test_fft_classifier_random_fifo]:
    factory = TestFactory(test)
    factory.add_option("input_mag", input_mag_values)
    factory.add_option("input_num", input_num_values)
    factory.add_option("cutoff_freq", cutoff_freq_values)
    factory.add_option("cutoff_mag", cutoff_mag_values)
    factory.add_option("sampling_freq", sampling_freq_values)
    factory.generate_tests()

# Composite test that combines loopback and FFT.
@cocotb.test()
async def test_compose(dut):
    msgs1 = [0x5555, 0xAAAA]
    inxbar_in_msgs = [mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_ARBITER)]
    inxbar_in_msgs += [mk_spi_pkt(RouterOut.IN_XBAR, x) for x in msgs1]
    inxbar_out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, x) for x in msgs1]

    msgs2 = [0xAAAA, 0x5555]
    clsxbar_in_msgs = [mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_ARBITER)]
    clsxbar_in_msgs += [mk_spi_pkt(RouterOut.CLS_XBAR, x) for x in msgs2]
    clsxbar_out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, x) for x in msgs2]

    assert False, "to be implemented"

"""
================================================================================
LBIST TESTS
================================================================================
"""

@cocotb.test()
async def test_lbist_fft1(dut):
    input_msgs = []

    # Configure crossbars to send data along this path: LFSR -> FFT1 -> MISR
    input_msgs += [mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.LFSR_FFT1)]
    input_msgs += [mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_MISR)]

    # Send 1 to LBIST controller to start LBIST test
    input_msgs += [mk_spi_pkt(RouterOut.LBIST_CTRL, 1)]

    # Expect to receive an 8-bit integer of 1s, to signify 8 passed tests
    output_msgs = [mk_spi_pkt(ArbiterIn.LBIST_CTRL, 0b11111111)]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, input_msgs, output_msgs)

@cocotb.test()
async def test_lbist_fft2(dut):
    input_msgs = []

    # Configure crossbars to send data along this path: LFSR -> FFT2 -> MISR
    input_msgs += [mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.LFSR_FFT2)]
    input_msgs += [mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_MISR)]

    # Send 1 to LBIST controller to start LBIST test
    input_msgs += [mk_spi_pkt(RouterOut.LBIST_CTRL, 1)]

    # Expect to receive an 8-bit integer of 1s, to signify 8 passed tests
    output_msgs = [mk_spi_pkt(ArbiterIn.LBIST_CTRL, 0b11111111)]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, input_msgs, output_msgs)

"""
================================================================================
PRESSURE TESTS
Tests for:
 - fill things up, see if the right things go through
================================================================================
"""
async def pressure_test(dut):
    pass
