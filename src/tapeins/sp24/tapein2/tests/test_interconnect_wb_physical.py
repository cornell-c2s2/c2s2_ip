import pytest

from src.tapeins.sp24.tapein2.tests.test_interconnect_physical import *

import random
from pymtl3 import *
from pymtl3.stdlib.stream.ifcs import valrdy_to_str
from pymtl3.stdlib.test_utils import (
    mk_test_case_table,
    run_sim,
    config_model_with_cmdline_opts,
)

"""
Ports we need to test:
 - Read port 0 (input xbar)     - wbostream
 - Read port 1 (classifer xbar) - wbostream
 - Read port 2 (output xbar)    - wbostream

 - Write port 0 (input xbar)     - wbistream
 - Write port 1 (classifer xbar) - wbistream
 - Write port 2 (output xbar)    - wbistream

Tests we can write
 - Loop back -> does not check the data
 - Blink -> Check the data on the processor (not sure how to write...)


Test 1: input xbar     -> read0 -> write1 -> classifer xbar
Test 2: input xbar     -> read0 -> write2 -> output xbar
Test 3: classifer xbar -> read1 -> write0 -> input xbar
Test 4: classifer xbar -> read1 -> write2 -> output xbar
Test 5: output xbar    -> read2 -> write0 -> input xbar
Test 6: output xbar    -> read2 -> write1 -> classifer xbar
"""

# ------------------------------------------------------------------------
# Message generation for loopback tests
# ------------------------------------------------------------------------

# Generates input/output msgs for spi -> inXbar -> wb -> clsXbar -> spi
def wb_loopback_inXbar_clsXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        input_xbar_config_msg(InXbarCfg.SPI_WSB),
        cls_xbar_config_msg(ClsXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> inXbar -> wb -> outXbar -> spi
# Because output xbar only takes the LSB of the wishbone output,
# the expected message from xbar is the LSB of the input message (msgs & 1)
def wb_loopback_inXbar_outXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        input_xbar_config_msg(InXbarCfg.SPI_WSB),
        output_xbar_config_msg(OutXbarCfg.WSB_SPI)
        ] + msgs, msgs & 1

# Generates input/output msgs for spi -> clsXbar -> wb -> inXbar -> spi
def wb_loopback_clsXbar_inXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        cls_xbar_config_msg(ClsXbarCfg.SPI_WSB),
        input_xbar_config_msg(InXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> clsXbar -> wb -> outXbar -> spi
# The expected message from xbar is the LSB of the input message (msgs & 1)
def wb_loopback_clsXbar_outXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        cls_xbar_config_msg(ClsXbarCfg.SPI_WSB),
        output_xbar_config_msg(OutXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> outXbar -> wb -> inXbar -> spi
def wb_loopback_outXbar_inXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10
    return [
        output_xbar_config_msg(OutXbarCfg.SPI_WSB),
        input_xbar_config_msg(InXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> outXbar -> wb -> clsXbar -> spi
def wb_loopback_outXbar_clsXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10
    return [
        output_xbar_config_msg(OutXbarCfg.SPI_WSB),
        cls_xbar_config_msg(ClsXbarCfg.WSB_SPI)
        ] + msgs, msgs

# ------------------------------------------------------------------------
# Loopback tests
# ------------------------------------------------------------------------

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
def test_wb_loopback_inXbar_clsXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = wb_loopback_inXbar_clsXbar_msg(msgs)
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
def test_wb_loopback_inXbar_outXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = wb_loopback_inXbar_outXbar_msg(msgs)
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
def test_wb_loopback_clsXbar_inXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = wb_loopback_clsXbar_inXbar_msg(msgs)
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
def test_wb_loopback_clsXbar_outXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = wb_loopback_clsXbar_outXbar_msg(msgs)
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
def test_wb_loopback_outXbar_inXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = wb_loopback_outXbar_inXbar_msg(msgs)
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
def test_wb_loopback_outXbar_clsXbar(msgs, cmdline_opts):
    in_msgs, out_msgs = wb_loopback_outXbar_clsXbar_msg(msgs)
    dut = make_interconnect(cmdline_opts)
    run_interconnect(dut, in_msgs, out_msgs)
