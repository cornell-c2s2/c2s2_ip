# --------------------------------------------------------------
#
#   spi_stream_protocol.py
#   Constructs logical low-level protocol messages to a dut or whatever.
#   Written by Will Salcedo '23
#
# --------------------------------------------------------------
from pymtl3 import *

def write_msg(payload: Bits) -> Bits:
    return concat(Bits2(0b10), payload)

def read_msg() -> Bits:
    return concat(Bits2(0b01), Bits20(0))

def write_read_msg(payload: Bits) -> Bits:
    return concat(Bits2(0b11), payload)

def nocommand_read_msg() -> Bits:
    return concat(Bits2(0b00), Bits20(0))

# def write_msg(payload, nbits):
#     return (0b10 << nbits) + payload

# def read_msg(nbits):
#     return 0b010 << nbits

# def write_read_msg(payload, nbits):
#     return (0b11 << nbits) + payload

# def nocommand_read_msg():
#     return 0b0000