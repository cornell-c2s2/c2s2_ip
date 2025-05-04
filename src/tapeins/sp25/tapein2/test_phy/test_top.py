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

from src.tapeins.sp25.tapein2.test_phy.spi_interface import *
from src.classifier.sim import classify
from src.fft.tests.fft import FFTInterface, FFTPease
from tools.utils import fixed_bits

import src.tapeins.sp25.tapein2.test_phy.phy_helpers as phy

if cocotb.simulator.is_running():
    ADDR_BITS = int(cocotb.top.ADDR_BITS.value)
    DATA_BITS = int(cocotb.top.DATA_BITS.value)
    SPI_PACKET_BITS = int(cocotb.top.SPI_PACKET_BITS.value)


USB_PORT = "ttyUSB0"


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

        # The following logging statements are for debugging purposes. Feel free
        # to modify them as needed.
        # dut._log.info("\nnew loop!")
        # dut._log.info(f"in_idx is {in_idx}, out_idx is {out_idx}")
        # dut._log.info(f"spc = {spc}")
        # dut._log.info(f"router_2_clsxbar_val = {dut.Router_to_ClassifierXbarDeserializer_val.value}")
        # dut._log.info(f"router_2_clsxbar_rdy = {dut.Router_to_ClassifierXbarDeserializer_rdy.value}")


        if in_idx < len(in_msgs) and spc == 1:
            # spi_status, retmsg = await spi_write_read(dut, in_msgs[in_idx])
            spi_status, retmsg = await spi_write_read(in_msgs[in_idx])

            dut._log.info(f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}, sending in {hex(in_msgs[in_idx])}")
            spc = spi_status[0]

            if spi_status[1] == 1:
                assert retmsg == out_msgs[out_idx]
                out_idx += 1
            in_idx += 1

        else:
            # spi_status, retmsg = await spi_read(dut)
            spi_status, retmsg = await spi_read()
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
    phy.set_for_test(USB_PORT)
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
    ROUTER_FFT1    = 0b1000
    ROUTER_FFT2    = 0b1001
    LFSR_FFT1      = 0b0000
    LFSR_FFT2      = 0b0001

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
    CLS_XBAR_DESERIALIZER  = 0b0011
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

    phy.set_for_test(USB_PORT)
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

    phy.set_for_test(USB_PORT)
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
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.CLS_XBAR_DESERIALIZER, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, msg) for msg in msgs]

    phy.set_for_test(USB_PORT)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=1000)

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

    phy.set_for_test(USB_PORT)
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

for test in [test_loopback_noXbar, test_loopback_inXbar, test_loopback_outXbar]:
    factory = TestFactory(test)
    factory.add_option("msgs", msgs_values)
    factory.generate_tests()


msgs_values_classifier_xbar = [
    # As of 04/24/2025, CLASSIFIER_SAMPLES = 16
    # 16-entry arrays
    [0xABCD, 0x1234, 0x5678, 0x9ABC, 0xDEF0, 0xABCD, 0x1234, 0x5678,
     0x9ABC, 0xDEF0, 0xDEF0, 0xABCD, 0x1234, 0x5678, 0x9ABC, 0xDEF0],
    [0x1A2B, 0x3C4D, 0x5E6F, 0x7A8B, 0x9C0D, 0x1A2B, 0x3C4D, 0x5E6F,
     0x7A8B, 0x9C0D, 0x1A2B, 0x3C4D, 0x5E6F, 0x7A8B, 0x9C0D, 0x1A2B],
    [0xBEEF, 0xC0DE, 0xFACE, 0xDEAD, 0xFEED, 0xC0DE, 0xBEEF, 0xFACE,
     0xDEAD, 0xFEED, 0xC0DE, 0xBEEF, 0xFACE, 0xDEAD, 0xFEED, 0xC0DE],
    [0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE, 0xFFFF, 0x0001, 0x0022,
     0x0033, 0x0044, 0x0055, 0x0066, 0x0077, 0x0088, 0x0099, 0x00AA],
    [0x1111, 0x2222, 0x3333, 0x4444, 0x5555, 0x6666, 0x7777, 0x8888,
     0x9999, 0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE, 0xFFFF, 0x0000],
    [0x1357, 0x2468, 0x369C, 0x48AF, 0x579D, 0x68BE, 0x79CD, 0x8ADE,
     0x9BDF, 0xACF0, 0xBDF1, 0xCEF2, 0xDFF3, 0xEFF4, 0xF0F5, 0x01F6],

    # 32-entry arrays
    [0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE, 0xAAAA, 0xBBBB, 0xCCCC,
     0xDDDD, 0xEEEE, 0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE, 0xAAAA,
     0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE, 0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD,
     0xEEEE, 0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE, 0xAAAA, 0xBBBB],
    [0x1001, 0x2002, 0x3003, 0x4004, 0x5005, 0x6006, 0x7007, 0x8008,
     0x9009, 0xA00A, 0xB00B, 0xC00C, 0xD00D, 0xE00E, 0xF00F, 0x0000,
     0x1001, 0x2002, 0x3003, 0x4004, 0x5005, 0x6006, 0x7007, 0x8008,
     0x9009, 0xA00A, 0xB00B, 0xC00C, 0xD00D, 0xE00E, 0xF00F, 0x0000],
    [0x1111, 0x3333, 0x5555, 0x7777, 0x9999, 0xBBBB, 0xDDDD, 0xFFFF,
     0x0F0F, 0x1F1F, 0x2F2F, 0x3F3F, 0x4F4F, 0x5F5F, 0x6F6F, 0x7F7F,
     0x8F8F, 0x9F9F, 0xAFAF, 0xBFBF, 0xCFCF, 0xDFDF, 0xEFEF, 0xFFFF,
     0xAAAA, 0x9999, 0x8888, 0x7777, 0x6666, 0x5555, 0x4444, 0x3333],
    [0xAB12, 0xBC23, 0xCD34, 0xDE45, 0xEF56, 0xF067, 0x1078, 0x2189,
     0x329A, 0x43AB, 0x54BC, 0x65CD, 0x76DE, 0x87EF, 0x98F0, 0xA901,
     0xBA12, 0xCB23, 0xDC34, 0xED45, 0xFE56, 0x0F67, 0x1F78, 0x2F89,
     0x3F9A, 0x4FAB, 0x5FBC, 0x6FCD, 0x7FDE, 0x8FEF, 0x9FF0, 0xAFF1],
    [0xACE1, 0xBDF2, 0xCEF3, 0xDFF4, 0xE0F5, 0xF1F6, 0x02F7, 0x13F8,
     0x24F9, 0x35FA, 0x46FB, 0x57FC, 0x68FD, 0x79FE, 0x8AFF, 0x9B00,
     0xAC01, 0xBD02, 0xCE03, 0xDF04, 0xE005, 0xF106, 0x0207, 0x1308,
     0x2409, 0x350A, 0x460B, 0x570C, 0x680D, 0x790E, 0x8A0F, 0x9B10],

    # 48-entry arrays
    [0x0001, 0x0011, 0x0021, 0x0031, 0x0041, 0x0051, 0x0061, 0x0071,
     0x0081, 0x0091, 0x00A1, 0x00B1, 0x00C1, 0x00D1, 0x00E1, 0x00F1,
     0x0101, 0x0111, 0x0121, 0x0131, 0x0141, 0x0151, 0x0161, 0x0171,
     0x0181, 0x0191, 0x01A1, 0x01B1, 0x01C1, 0x01D1, 0x01E1, 0x01F1,
     0x0201, 0x0211, 0x0221, 0x0231, 0x0241, 0x0251, 0x0261, 0x0271,
     0x0281, 0x0291, 0x02A1, 0x02B1, 0x02C1, 0x02D1, 0x02E1, 0x02F1],
    [0xFACE, 0xC0DE, 0xBEEF, 0xFEED, 0xDEAD, 0xCAFE, 0xBABE, 0xF00D,
     0xABBA, 0xD00D, 0xFEEF, 0xBADA, 0xBEEF, 0xFACE, 0xF00D, 0xC0DE,
     0xBABE, 0xFEED, 0xDEAD, 0xCAFE, 0xABBA, 0xD00D, 0xFEEF, 0xBADA,
     0xFACE, 0xC0DE, 0xBEEF, 0xFEED, 0xDEAD, 0xCAFE, 0xBABE, 0xF00D,
     0xABBA, 0xD00D, 0xFEEF, 0xBADA, 0xBEEF, 0xFACE, 0xF00D, 0xC0DE,
     0xBABE, 0xFEED, 0xDEAD, 0xCAFE, 0xABBA, 0xD00D, 0xFEEF, 0xBADA],
    [0x7777, 0x8888, 0x9999, 0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE,
     0xFFFF, 0x0000, 0x1111, 0x2222, 0x3333, 0x4444, 0x5555, 0x6666,
     0x7777, 0x8888, 0x9999, 0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE,
     0xFFFF, 0x0000, 0x1111, 0x2222, 0x3333, 0x4444, 0x5555, 0x6666,
     0x7777, 0x8888, 0x9999, 0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE,
     0xFFFF, 0x0000, 0x1111, 0x2222, 0x3333, 0x4444, 0x5555, 0x6666],
    [0x1A2A, 0x2B3B, 0x3C4C, 0x4D5D, 0x5E6E, 0x6F7F, 0x7F8F, 0x8F9F,
     0x9FAF, 0xAFCF, 0xCFDF, 0xDFEF, 0xEFF0, 0xF001, 0x1022, 0x2033,
     0x3044, 0x4055, 0x5066, 0x6077, 0x7088, 0x8099, 0x90AA, 0xA0BB,
     0xB0CC, 0xC0DD, 0xD0EE, 0xE0FF, 0xF011, 0x1022, 0x2033, 0x3044,
     0x4055, 0x5066, 0x6077, 0x7088, 0x8099, 0x90AA, 0xA0BB, 0xB0CC,
     0xC0DD, 0xD0EE, 0xE0FF, 0xF011, 0x1022, 0x2033, 0x3044, 0x4055],
    [0xCAF1, 0xDBE2, 0xECF3, 0xFDF4, 0x0EF5, 0x1FF6, 0x30F7, 0x41F8,
     0x52F9, 0x63FA, 0x74FB, 0x85FC, 0x96FD, 0xA7FE, 0xB8FF, 0xC900,
     0xDA01, 0xEB02, 0xFC03, 0x0D04, 0x1E05, 0x2F06, 0x4007, 0x5108,
     0x6209, 0x730A, 0x840B, 0x950C, 0xA60D, 0xB70E, 0xC80F, 0xD910,
     0xEA11, 0xFB12, 0x0C13, 0x1D14, 0x2E15, 0x3F16, 0x5017, 0x6118,
     0x7219, 0x831A, 0x941B, 0xA51C, 0xB61D, 0xC71E, 0xD81F, 0xE920]
]


# Classifier loopback uses different input messages due to classifier xbar deserializer. The deserializer 
# will only send a valid output after receiving CLASSIFIER_SAMPLES number of messages. 
for test in [test_loopback_clsXbar]:
    factory = TestFactory(test)
    factory.add_option("msgs", msgs_values_classifier_xbar)
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

"""
-----------
FFT1 TESTS
-----------
"""
def fft1_msg(inputs: list[Fixed], outputs: list[Fixed]):
    """Generate SPI packets for FFT input/output from fixed-point numbers."""
    
    #ensure that input and output samples are converted from fixed to bits
    inputs = [fixed_bits(sample) for sample in inputs[0]]
    outputs = [fixed_bits(sample) for sample in outputs[0]]

    #configure input and output crossbars to send messages to/receive messages from FFT1
    in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1)
    out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_ARBITER)
    
    # send fft inputs to router and fft outputs to Arbiter from XBar
    fft_input_msgs = [mk_spi_pkt(RouterOut.IN_XBAR, int(x)) for x in inputs]
    fft_output_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, int(x)) for x in outputs]

    #complete input and output message configurations
    in_msgs = [in_xbar_config_msg, out_xbar_config_msg] + fft_input_msgs
    out_msgs =  fft_output_msgs
    
    return in_msgs, out_msgs

async def test_fft1_manual(dut, input, output):
    in_msgs, out_msgs = fft1_msg(input, output)
    phy.set_for_test(USB_PORT)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=100)

"""
-----------
FFT2 TESTS
-----------
"""
def fft2_msg(inputs: list[Fixed], outputs: list[Fixed]):
    """Generate SPI packets for FFT input/output from fixed-point numbers."""
    
    #ensure that input and output samples are converted from fixed to bits
    inputs = [fixed_bits(sample) for sample in inputs[0]]
    outputs = [fixed_bits(sample) for sample in outputs[0]]

    #configure input and output crossbars to send messages to/receive messages from FFT2
    in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT2)
    out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_ARBITER)
    
    # send fft inputs to router and fft outputs to Arbiter from XBar
    fft_input_msgs = [mk_spi_pkt(RouterOut.IN_XBAR, int(x)) for x in inputs]
    fft_output_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, int(x)) for x in outputs]

    #complete input and output message configurations
    in_msgs = [in_xbar_config_msg, out_xbar_config_msg] + fft_input_msgs
    out_msgs =  fft_output_msgs
    
    return in_msgs, out_msgs

async def test_fft2_manual(dut, input, output):
    in_msgs, out_msgs = fft2_msg(input, output)
    phy.set_for_test(USB_PORT)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, max_trsns=100)

"""
-----------
RUN FFT TESTS
-----------
"""
# Test Data
input_values = [
    [[fixN(1) for _ in range(32)]]
]

output_values = [
    [[fixN(32)] + [fixN(0) for _ in range(15)]]
]

# Register test factory
for test in [test_fft1_manual, test_fft2_manual]:
    factory = TestFactory(test)
    factory.add_option("input", input_values)
    factory.add_option("output", output_values)
    factory.generate_tests()



"""
================================================================================
CLASSIFIER TESTS
================================================================================
"""
def classifier_msg(inputs: list[Fixed], outputs: list[int]):
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

    in_msgs = [
        mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_CLS),
        mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.CLS_ARBITER)
    ] + [mk_spi_pkt(RouterOut.CLS_XBAR_DESERIALIZER, x) for x in inputs]

    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, x) for x in outputs]

    return in_msgs, out_msgs

@cocotb.test()
async def test_classifier_manual(dut):
    in_msgs, out_msgs = classifier_msg([[fixN(1) for _ in range(16)]], [0x0000])
    phy.set_for_test(USB_PORT)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)


"""
================================================================================
FFT -> CLASSIFIER TESTS
Tests for:
- spi -> router -> input xbar -> fft -> classifier xbar -> classifier -> output xbar -> arbiter -> spi
================================================================================
"""
async def test_fft_classifier_random(dut, input_mag, input_num, cutoff_freq, cutoff_mag, sampling_freq):
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

    phy.set_for_test(USB_PORT)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, inputs, outputs, max_trsns=1000)

input_mag_values =[1, 10]
input_num_values =[1, 10]
cutoff_freq_values = [0, 2000]
cutoff_mag_values = [0.7, 2.3]
sampling_freq_values = [44800, 44100, 25000]

factory = TestFactory(test_fft_classifier_random)
factory.add_option("input_mag", input_mag_values)
factory.add_option("input_num", input_num_values)
factory.add_option("cutoff_freq", cutoff_freq_values)
factory.add_option("cutoff_mag", cutoff_mag_values)
factory.add_option("sampling_freq", sampling_freq_values)
factory.generate_tests()

# Composite test that combines loopback and FFT.
# @cocotb.test()
async def test_compose(dut):
    msgs1 = [0x5555, 0xAAAA]
    inxbar_in_msgs = [mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_ARBITER)] \
      + [mk_spi_pkt(RouterOut.IN_XBAR, x) for x in msgs1]
    inxbar_out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, x) for x in msgs1]


    msgs2 = [0xAAAA, 0x5555]    
    clsxbar_in_msgs = [mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_ARBITER)] \
      + [mk_spi_pkt(RouterOut.CLS_XBAR_DESERIALIZER, x) for x in msgs2]
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

    phy.set_for_test(USB_PORT)
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

    phy.set_for_test(USB_PORT)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, input_msgs, output_msgs)