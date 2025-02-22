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

# Generates input/output msgs for spi -> inXbar -> wb -> clsXbar -> spi
def wb_loopback_inXbar_clsXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        input_xbar_config_msg(InXbarCfg.SPI_WSB),
        cls_xbar_config_msg(ClsXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> inXbar -> wb -> outXbar -> spi
def wb_loopback_inXbar_outXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        input_xbar_config_msg(InXbarCfg.SPI_WSB),
        output_xbar_config_msg(OutXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> clsXbar -> wb -> inXbar -> spi
def wb_loopback_clsXbar_inXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        cls_xbar_config_msg(ClsXbarCfg.SPI_WSB),
        input_xbar_config_msg(InXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> clsXbar -> wb -> outXbar -> spi
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
        assert x >= 0 and x < 0x10000
    return [
        output_xbar_config_msg(OutXbarCfg.SPI_WSB),
        input_xbar_config_msg(InXbarCfg.WSB_SPI)
        ] + msgs, msgs

# Generates input/output msgs for spi -> outXbar -> wb -> clsXbar -> spi
def wb_loopback_outXbar_clsXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [
        output_xbar_config_msg(OutXbarCfg.SPI_WSB),
        cls_xbar_config_msg(ClsXbarCfg.WSB_SPI)
        ] + msgs, msgs