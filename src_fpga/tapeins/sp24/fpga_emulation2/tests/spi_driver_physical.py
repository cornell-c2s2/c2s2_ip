from pymtl3 import *
from spidriver import SPIDriver
import time

s = SPIDriver("COM7")


def spi_write_physical(dut, src_msg):
    src_msg_bytes = []

    while src_msg.nbits > 8:
        src_msg_bytes.append(int(src_msg[src_msg.nbits - 8 : src_msg.nbits]))
        src_msg = src_msg[: src_msg.nbits - 8]
    src_msg_bytes.append(int(src_msg))
    s.sel()
    # time.sleep(0.05)
    readbytes = s.writeread(src_msg_bytes)

    s.unsel()
    # time.sleep(0.05)
    # return Bits40(int.from_bytes(readbytes, "big"))

    return Bits40(int.from_bytes(readbytes, "big") >> 2)


def spi_reset_a():
    """
    Set the FPGA reset signal high by toggling A on the SPI driver
    """
    s.seta(1)
    time.sleep(0.05)
    s.seta(0)
    time.sleep(0.05)
