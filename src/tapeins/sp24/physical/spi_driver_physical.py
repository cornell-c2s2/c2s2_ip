from pymtl3 import *
from spidriver import SPIDriver
import time

# set `tests_on_c2` to `True` if operating physical tests on c2
tests_on_c2 = False
s = SPIDriver("/dev/ttyUSB0") if tests_on_c2 else SPIDriver("COM7")


def spi_write_physical(dut, src_msg):
    src_msg_bytes = []

    while src_msg.nbits > 8:
        src_msg_bytes.append(int(src_msg[src_msg.nbits - 8 : src_msg.nbits]))
        src_msg = src_msg[: src_msg.nbits - 8]
    src_msg_bytes.append(int(src_msg))
    s.sel()

    readbytes = s.writeread(src_msg_bytes)

    s.unsel()

    return Bits40(int.from_bytes(readbytes, "big") >> 2)


def spi_reset_a():
    """
    Set the FPGA reset signal high by toggling A on the SPI driver
    """
    s.seta(1)
    time.sleep(0.05)
    s.seta(0)
    time.sleep(0.05)