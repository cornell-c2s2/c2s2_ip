from pymtl3 import *
from spidriver import SPIDriver
from spi_stream_protocol import *

s = SPIDriver("\\\\.\\COM3")


class InXbarCfg(int):
    SPI_SPI = 0b0000  # SPI loopback
    SPI_WSB = 0b0001  # SPI to Wishbone
    SPI_FFT = 0b0010  # SPI to FFT

    WSB_SPI = 0b0100  # Wishbone to SPI
    WSB_FFT = 0b0101  # Wishbone to FFT
    WSB_WSB = 0b0110  # Wishbone looback


class ClsXbarCfg(int):
    SPI_SPI = 0b0000  # SPI loopback
    SPI_WSB = 0b0001  # SPI to Wishbone
    SPI_CLS = 0b0010  # SPI to Classifier

    WSB_SPI = 0b0100  # Classifier to SPI
    WSB_WSB = 0b0101  # Wishbone loopback
    WSB_CLS = 0b0110  # Wishbone to Classifier

    FFT_SPI = 0b1000  # FFT to SPI
    FFT_WSB = 0b1001  # FFT to Wishbone
    FFT_CLS = 0b1010  # FFT to Classifier


class OutXbarCfg(int):
    SPI_SPI = 0b0000  # SPI loopback
    SPI_WSB = 0b0001  # SPI to Wishbone

    WSB_SPI = 0b0100  # Wishbone to SPI
    WSB_WSB = 0b0101  # Wishbone loopback

    CLS_SPI = 0b1000  # Classifier to SPI
    CLS_WSB = 0b1001  # Classifier to Wishbone


class ClsCfgType(int):
    CTF_FRQ = 6  # Cut-off frequency
    CTF_MAG = 7  # Cut-off Magnitude
    SMP_FRQ = 8  # Sampling Frequency


# Generates classifier config messages
def cls_config_msg(config: ClsCfgType, value: int):
    assert value < 0x10000 and value >= 0
    return (config << 16) | value


# Generates xbar config messages
def input_xbar_config_msg(config: InXbarCfg):
    assert config < 16 and config >= 0
    return 0x10000 | config


# Generates xbar config messages
def cls_xbar_config_msg(config: ClsXbarCfg):
    assert config < 16 and config >= 0
    return 0x30000 | config


# Generates xbar config messages
def output_xbar_config_msg(config: OutXbarCfg):
    assert config < 16 and config >= 0
    return 0x50000 | config


# Generates input/output msgs for inXbar loopback
def loopback_inXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    return [input_xbar_config_msg(InXbarCfg.SPI_SPI)] + msgs, msgs


# Generates input/output msgs for clsXbar loopback
def loopback_clsXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10000
    new_msgs = [(0x20000 | int(x)) for x in msgs]
    return [cls_xbar_config_msg(ClsXbarCfg.SPI_SPI)] + new_msgs, new_msgs


# Generates input/output msgs for outXbar loopback
def loopback_outXbar_msg(msgs):
    for x in msgs:
        assert x >= 0 and x < 0x10
    new_msgs = [(0x40000 | int(x)) for x in msgs]
    return [output_xbar_config_msg(OutXbarCfg.SPI_SPI)] + new_msgs, new_msgs

def spi_write_physical(dut, src_msg):
    src_msg_bytes = []

    while src_msg.nbits > 8:
        src_msg_bytes.append(int(src_msg[src_msg.nbits - 8 : src_msg.nbits]))
        src_msg = src_msg[: src_msg.nbits - 8]
    src_msg_bytes.append(int(src_msg))
    s.sel()
    readbytes = s.writeread(src_msg_bytes)

    s.unsel()
    
    print("readbytes: ", hex(int.from_bytes(readbytes, "big")))

    return Bits40(int.from_bytes(readbytes, "big"))

spi_write_physical(s, read_msg())
spi_write_physical(s, write_msg(0x1234))