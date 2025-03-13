from cocotb.triggers import ClockCycles
from dataclasses import dataclass

from pymtl3 import *

async def tr(dut, cs: int, sclk: int, mosi: int) -> int:

    dut.cs.value = cs
    dut.sclk.value = sclk
    dut.mosi.value = mosi
    try:
        retval = int(dut.miso.value)
    except:
        dut._log.info(f"miso is {dut.miso.value}, type is {type(dut.miso.value)}")
        assert False

    await ClockCycles(dut.clk, 1)
    return retval



# Writes/Reads an SPI transaction. Lowest level of abstraction.
async def _spi_write(dut, src_msg: Bits) -> Bits:
    
    packet_size = src_msg.nbits
    snk_msg = Bits(src_msg.nbits)

    await tr(dut, 1, 0, 0)

    for i in range(packet_size):
        await tr(dut, 0, 0, 0)
        await tr(dut, 0, 0, int(src_msg[packet_size - i - 1]))
        await tr(dut, 0, 1, int(src_msg[packet_size - i - 1]))
        await tr(dut, 0, 1, 0)
        snk_msg[packet_size - i - 1] = await tr(dut, 0, 0, 0)
    
    await tr(dut, 1, 0, 0)
    
    return snk_msg[packet_size-2:packet_size], snk_msg[0:packet_size-2]

# TODO: need to update bits to be relative to spi_packet's size 
async def spi_read(dut):
    return await _spi_write(dut, concat(Bits2(0b01), Bits20(0)))

async def spi_write(dut, spi_packet):
    return await _spi_write(dut, concat(Bits2(0b10), spi_packet))

async def spi_write_read(dut, spi_packet):
    return await _spi_write(dut, concat(Bits2(0b11), spi_packet))