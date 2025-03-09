import random
from enum import Enum

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory
from pymtl3 import *

from src.tapeins.sp25.tapein1.tests.spi_driver_sim import spi_write
from src.tapeins.sp25.tapein1.tests.spi_stream_protocol import *

if cocotb.simulator.is_running():
    ADDR_BITS = int(cocotb.top.ADDR_BITS.value)
    DATA_BITS = int(cocotb.top.DATA_BITS.value)
    SPI_PACKET_BITS = int(cocotb.top.SPI_PACKET_BITS.value)


async def run_top(dut, in_msgs, out_msgs, max_trsns=30, curr_trsns=0):
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

        if in_idx < len(in_msgs) and spc == 1:
            # retmsg = await spi_write(dut, write_read_msg(in_msgs[in_idx], SPI_PACKET_BITS), SPI_PACKET_BITS + 2)
            retmsg = await spi_write(dut, write_read_msg(in_msgs[in_idx]))
            dut._log.info(f"Trns {trsns}: {spc} | {hex(retmsg)}, sending in {hex(in_msgs[in_idx])}")
            spc = retmsg[20]
            
            if retmsg[SPI_PACKET_BITS + 1] == 1:
                assert retmsg[0:SPI_PACKET_BITS] == out_msgs[out_idx]
                out_idx += 1
            in_idx += 1
        
        else:
            retmsg = await spi_write(dut, read_msg())
            dut._log.info(f"Trns {trsns}: {spc} | {hex(retmsg)}")
            spc = retmsg[SPI_PACKET_BITS]
            if retmsg[SPI_PACKET_BITS + 1] == 1:
                assert retmsg[0:SPI_PACKET_BITS] == out_msgs[out_idx]
                out_idx += 1

        trsns += 1

    return trsns - 1

        

@cocotb.test()
async def basic_test(dut):
    """Check if things compile!"""
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 10)
    assert True

class InXbarCfg:
    ROUTER_ARBITER = 0b1111

class ClsXbarCfg:
    ROUTER_ARBITER = 0b1111

class OutXbarCfg:
    # ROUTER_ARBITER = 0b110
    ROUTER_ARBITER = 0b101


class RouterOut:
    LBIST_CTRL             = 0b0000
    IN_XBAR                = 0b0001
    IN_XBAR_CTRL           = 0b0010
    CLS_XBAR               = 0b0011
    CLS_XBAR_CTRL          = 0b0100
    CLS_XBAR_CUT_FREQ_CTRL = 0b0101
    CLS_XBAR_MAG_CTRL      = 0b0110
    OUT_XBAR               = 0b1000
    OUT_XBAR_CTRL          = 0b1001
    ARBITER                = 0b1010


class ArbiterIn:
    ROUTER     = 0
    IN_XBAR    = 1
    CLS_XBAR   = 2
    OUT_XBAR   = 3
    LBIST_CTRL = 4


async def reset_dut(dut):
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    await ClockCycles(dut.clk, 3)

def mk_spi_pkt(addr: int, data: int):
    """Make spi packet"""
    assert not data >> DATA_BITS
    assert not addr >> ADDR_BITS
    return (addr << DATA_BITS) | data

async def test_loopback_noXbar(dut, msgs):
    # cfg_msg = mk_spi_pkt(RouterOut.ARBITER, 0)
    in_msgs = [mk_spi_pkt(RouterOut.ARBITER, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.ROUTER, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_inXbar(dut, msgs):
    cfg_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_ARBITER)
    in_msgs = [cfg_msg] + [mk_spi_pkt(RouterOut.IN_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_clsXbar(dut, msgs):
    cfg_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_ARBITER)
    in_msgs = [cfg_msg] + [mk_spi_pkt(RouterOut.CLS_XBAR, x) for x in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

async def test_loopback_outXbar(dut, msgs):
    cfg_msg = mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.ROUTER_ARBITER)
    in_msgs = [cfg_msg] + [mk_spi_pkt(RouterOut.OUT_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs)

"""
Generate tests here using test factory to test for different messages, kind of
like with pytest parameters
"""
# Test Input Crossbar Loopback
msgs_values = [
        [0xFFFF],
        [0x0000],
        [0x5555, 0xAAAA],
        [0xAAAA, 0x5555],
        [0xDEAD, 0xBEEF, 0xCAFE, 0xBABE],
        [0xABCD, 0x1234, 0x5678, 0x9ABC, 0xDEF0]
]
# for test in [test_loopback_noXbar, test_loopback_inXbar, test_loopback_clsXbar, test_loopback_outXbar]:
for test in [test_loopback_outXbar]:
    factory = TestFactory(test)
    factory.add_option("msgs", msgs_values)
    factory.generate_tests()

