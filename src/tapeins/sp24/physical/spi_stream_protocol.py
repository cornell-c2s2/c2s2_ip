# --------------------------------------------------------------
#
#   spi_stream_protocol.py
#   Constructs logical low-level protocol messages to a dut or whatever.
#   Written by Will Salcedo '23
#
# --------------------------------------------------------------

from pymtl3 import *


def write_msg(payload: Bits) -> Bits:
    return concat(Bits4(0b10), payload)


def read_msg() -> Bits:
    return concat(Bits4(0b01), Bits20(0))


def write_read_msg(payload: Bits) -> Bits:
    return concat(Bits4(0b11), payload)


def nocommand_read_msg() -> Bits:
    return concat(Bits4(0b00), Bits20(0))