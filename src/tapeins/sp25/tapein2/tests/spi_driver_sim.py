from cocotb.triggers import ClockCycles
from dataclasses import dataclass

from pymtl3 import *

async def tr(dut, cs: int, sclk: int, mosi: int) -> int:
    """
    Toggle the SPI signals and return the value of miso.
    """

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
    """
    `_spi_write(dut, src_msg)` writes a SPI transaction to the DUT and return the response.
    The src_msg should be a Bits object containing the SPI packet to send.
    The response will be a Bits object containing the received data.

    Returns: A tuple of two Bits objects:
    - The first one is the status bits (2 bits) 
    - The second one is the data received from the SPI device (the rest of the bits).

    Note: The first two bits of the response are the status bits (0 for read, 1 for write).
    If we wanted our spi packets to be 20 bits long, src_msg should be 22 bits long (2 bits for transaction type + 20 bits for data).
    This should be handled by the functions that call _spi_write.
    """
    
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
    """
    `spi_read(dut)` reads a SPI transaction from the DUT and returns the response.

    Returns: A tuple of two Bits objects:
    - The first one is the status bits (2 bits) 
    - The second one is the data received from the SPI device (the rest of the bits).
    """
    return await _spi_write(dut, concat(Bits2(0b01), Bits20(0)))

async def spi_write(dut, spi_packet):
    """
    `spi_write(dut, spi_packet)` writes a SPI transaction to the DUT and returns the response.

    Returns: A tuple of two Bits objects:
    - The first one is the status bits (2 bits) 
    - The second one is the data received from the SPI device (the rest of the bits).
    """
    return await _spi_write(dut, concat(Bits2(0b10), spi_packet))

async def spi_write_read(dut, spi_packet):
    """
    `spi_write_read(dut, spi_packet)` writes a SPI transaction to the DUT and returns the response.
    This is a combined write and read operation.

    Returns: A tuple of two Bits objects:
    - The first one is the status bits (2 bits) 
    - The second one is the data received from the SPI device (the rest of the bits).
    """
    return await _spi_write(dut, concat(Bits2(0b11), spi_packet))
