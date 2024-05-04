import pytest
from src.tapeins.sp24.tapein1.tests.spi_driver_sim import spi_write
from src.tapeins.sp24.tapein1.interconnect import Interconnect
from src.tapeins.sp24.tapein1.tests.spi_stream_protocol import *

from pymtl3 import *
from pymtl3.stdlib.test_utils import (
    mk_test_case_table,
    run_sim,
    config_model_with_cmdline_opts,
)

max_trsns = 100


@pytest.mark.parametrize(
    "in_msgs, out_msgs",
    [([0x15555, 0x2AAAA], [0x15555, 0x2AAAA])],
)
def test_interconnect(in_msgs, out_msgs, cmdline_opts):
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

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"

        if in_idx < len(in_msgs) and spc == 1:
            retmsg = spi_write(dut, write_read_msg(in_msgs[in_idx]))
            in_idx += 1
            spc = retmsg[18]
            if retmsg[19] == 1:
                assert retmsg[0:18] == out_msgs[out_idx]
                out_idx += 1

        else:
            retmsg = spi_write(dut, nocommand_read_msg())
            spc = retmsg[18]
            if retmsg[19] == 1:
                assert retmsg[0:18] == out_msgs[out_idx]
                out_idx += 1

        trsns += 1
