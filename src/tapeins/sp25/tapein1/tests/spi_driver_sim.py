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
async def spi_write(dut, src_msg: Bits) -> Bits:
    
    packet_size = src_msg.nbits
    snk_msg = Bits(src_msg.nbits)

    await tr(dut, 1, 0, 0)


    # dut._log.info("\nspi_writing...")
    for i in range(packet_size):
        await tr(dut, 0, 0, 0)
        await tr(dut, 0, 0, int(src_msg[packet_size - i - 1]))
        await tr(dut, 0, 1, int(src_msg[packet_size - i - 1]))
        await tr(dut, 0, 1, 0)
        snk_msg[packet_size - i - 1] = await tr(dut, 0, 0, 0)
        # dut._log.info(f"i is {i}, snk_msg became {bin(snk_msg)}")
    
    await tr(dut, 1, 0, 0)
    
    # dut._log.info(f"snk_msg: {bin(snk_msg)}, packet_size is {packet_size}")
    return snk_msg
        


# async def tr(dut, cs: int, sclk: int, mosi: int) -> int:

#     dut.cs.value = cs
#     dut.sclk.value = sclk
#     dut.mosi.value = mosi
#     retval = dut.miso.value.integer
#     await ClockCycles(dut.clk, 1)
#     return retval

# # Writes/Reads an SPI transaction. Lowest level of abstraction.
# async def spi_write(dut, src_msg: int, packet_size: int) -> int:
#     await tr(dut, 1, 0, 0)

#     # dut._log.info("\nspi_writing...")
#     snk_msg = 0
#     for i in range(packet_size - 1, -1, -1):
#         await tr(dut, 0, 0, 0)
#         await tr(dut, 0, 0, (src_msg >> i) & 1)
#         await tr(dut, 0, 1, (src_msg >> i) & 1)
#         await tr(dut, 0, 1, 0)
#         snk_msg += (await tr(dut, 0, 0, 0)) << i
#         # dut._log.info(f"i is {i}, snk_msg became {bin(snk_msg)}")
    
#     await tr(dut, 1 ,0, 0)
    
#     # dut._log.info(f"snk_msg: {bin(snk_msg)}, packet_size is {packet_size}")
#     return snk_msg
        

