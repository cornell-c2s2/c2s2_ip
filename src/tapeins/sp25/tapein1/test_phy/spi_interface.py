"""
cli_interface.py

A file dedicated for the command-line interface between the SPI driver and the digital SP24 tape-out.

Author: Simeon Turner
"""

from pymtl3 import *
from spidriver import SPIDriver
import spi_stream_protocol
import time


"""
device                - an SPIDriver object; None when not initialized.
port                  - string defining which USB port this file is directing SPI Driver data to.
print_mode            - integer that determines how things are printed in terminal.
                          0 - prints nothing in terminal
                          1 - prints the transactions in terminal
                          2 - prints the classifier output in terminal
transaction_print_len - integer that determines how many bits to print when printing transactions.
                          Requires that 0 <= transaction_print_len < 40.
                          The lengths of interest are 20 and 24.
"""
device = None
port = None
print_mode = 0
transaction_print_len = 20


# ===================================== Functions for Settings =====================================

def init_usb(usb_port):
  """
  Re-initializes the global SPIDriver object to the USB port `port`. 
  
  Be sure to know which USB port to initialize to. If using Windows, open device manager 
  and look under 'Ports' to see which port the SPI driver connected to.
  """
  global device
  global port

  device = SPIDriver(usb_port)
  port = usb_port


def show_device_info():
  """
  Prints, in the command-line, the current information about the device and USB port.
  """
  print("\nYour current device is", device)
  print("You are connected through", port, "\n")


def set_print_mode(mode):
  """
  Sets the print mode to mode. This determines what is printed in terminal. Requires that
  mode is 0, 1, or 2.

  Modes:
    0 - prints nothing in terminal
    1 - prints the transactions in terminal
    2 - prints the classifier output in terminal
  """
  assert mode >=0 and mode <= 2

  global print_mode
  print_mode = mode


def set_transaction_print_len(integer):
  """
  Sets the transaction length to integer. This determines how many bits get printed on the 
  terminal when print_mode is 1.
  """
  assert integer >= 0 and integer < 40

  global transaction_print_len
  transaction_print_len = integer


# ===================================== Functions for SPI Communication =====================================
# Digital chip crossbar configuration messages
# Inspired from test_interconnect_physical.py
class Config(int):
  # Input crossbar configuration messages
  INXBAR_SPI_SPI = 0x10000  # SPI loopback
  INXBAR_SPI_WSB = 0x10001  # SPI to Wishbone
  INXBAR_SPI_FFT = 0x10002  # SPI to FFT

  INXBAR_WSB_SPI = 0x10004  # Wishbone to SPI
  INXBAR_WSB_FFT = 0x10005  # Wishbone to FFT
  INXBAR_WSB_WSB = 0x10006  # Wishbone looback

  # Classifier crossbar configuration messages
  CLSXBAR_SPI_SPI = 0x30000  # SPI loopback
  CLSXBAR_SPI_WSB = 0x30001  # SPI to Wishbone
  CLSXBAR_SPI_CLS = 0x30002  # SPI to Classifier

  CLSXBAR_WSB_SPI = 0x30004  # Classifier to SPI
  CLSXBAR_WSB_WSB = 0x30005  # Wishbone loopback
  CLSXBAR_WSB_CLS = 0x30006  # Wishbone to Classifier

  CLSXBAR_FFT_SPI = 0x30008  # FFT to SPI
  CLSXBAR_FFT_WSB = 0x30009  # FFT to Wishbone
  CLSXBAR_FFT_CLS = 0x3000a  # FFT to Classifier

  # Output crossbar configuration messages
  OUTXBAR_SPI_SPI = 0x50000  # SPI loopback
  OUTXBAR_SPI_WSB = 0x50001  # SPI to Wishbone

  OUTXBAR_WSB_SPI = 0x50004  # Wishbone to SPI
  OUTXBAR_WSB_WSB = 0x50005  # Wishbone loopback

  OUTXBAR_CLS_SPI = 0x50008  # Classifier to SPI
  OUTXBAR_CLS_WSB = 0x50009  # Classifier to Wishbone

  # Classifier cutoff configuration messages
  # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! TODO: CONVERT TO FUNCTIONS !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  CLS_CUTOFF_FREQ = 0x60000
  CLS_CUTOFF_MAG = 0x70000
  CLS_SAMP_FREQ = 0x80000


def spi_none():
  """
  Sends a message to the SPI driver with instruction "no command read".
  """
  send = spi_stream_protocol.nocommand_read_msg()
  recv = spi_write_physical(send)
  return send, recv
  

def spi_read():
  """
  Reads a message from the SPI driver.
  """
  send = spi_stream_protocol.read_msg()
  recv = spi_write_physical(send)
  return send, recv
  

def spi_write(message):
  """
  Writes a message to the SPI driver.
  """
  send = spi_stream_protocol.write_msg(mk_bits(20)(message))
  recv = spi_write_physical(send)
  return send, recv
  

def spi_write_read(message):
  """
  Writes a message and reads the output message from the SPI Driver.
  """
  send = spi_stream_protocol.write_read_msg(mk_bits(20)(message))
  recv = spi_write_physical(send)
  return send, recv


def spi_none_print():
  """
  Sends a message to the SPI driver with instruction "no command read".
  """
  send = spi_stream_protocol.nocommand_read_msg()
  recv = spi_write_physical(send)

  if print_mode == 1:
    print("Transaction:  " + str(send[0:transaction_print_len]) + "  >  " + 
        str(recv[0:transaction_print_len]))
  elif print_mode == 2:
    if recv[16:20] == mk_bits(4)(0x4):
      if recv[0] == mk_bits(1)(0x1):
        print("Classifier: 1")
      else:
        print("Classifier: 0")

  return send, recv
  

def spi_read_print():
  """
  Reads a message from the SPI driver.
  """
  send = spi_stream_protocol.read_msg()
  recv = spi_write_physical(send)
  
  if print_mode == 1:
    print("Transaction:  " + str(send[0:transaction_print_len]) + "  >  " + 
        str(recv[0:transaction_print_len]))
  elif print_mode == 2:
    if recv[16:20] == mk_bits(4)(0x4):
      if recv[0] == mk_bits(1)(0x1):
        print("Classifier: 1")
      else:
        print("Classifier: 0")

  return send, recv
  

def spi_write_print(message):
  """
  Writes a message to the SPI driver.
  """
  send = spi_stream_protocol.write_msg(mk_bits(20)(message))
  recv = spi_write_physical(send)
  
  if print_mode == 1:
    print("Transaction:  " + str(send[0:transaction_print_len]) + "  >  " + 
        str(recv[0:transaction_print_len]))
  elif print_mode == 2:
    if recv[16:20] == mk_bits(4)(0x4):
      if recv[0] == mk_bits(1)(0x1):
        print("Classifier: 1")
      else:
        print("Classifier: 0")

  return send, recv
  

def spi_write_read_print(message):
  """
  Writes a message and reads the output message from the SPI Driver.
  """
  send = spi_stream_protocol.write_read_msg(mk_bits(20)(message))
  recv = spi_write_physical(send)
  
  if print_mode == 1:
    print("Transaction:  " + str(send[0:transaction_print_len]) + "  >  " + 
        str(recv[0:transaction_print_len]))
  elif print_mode == 2:
    if recv[16:20] == mk_bits(4)(0x4):
      if recv[0] == mk_bits(1)(0x1):
        print("Classifier: 1")
      else:
        print("Classifier: 0")

  return send, recv


def spi_trigger_a(duration):
    """
    Sets the A signal on the SPI Driver high for duration seconds, and 
    sets it low for duration seconds
    """
    device.seta(1)
    time.sleep(duration)
    device.seta(0)
    time.sleep(duration)


def spi_trigger_b(duration):
    """
    Sets the A signal on the SPI Driver high for duration seconds, and 
    sets it low for duration seconds
    """
    device.setb(1)
    time.sleep(duration)
    device.setb(0)
    time.sleep(duration)



# ===================================== Helper Functions =====================================

def spi_write_physical(src_msg):
  """
  Written by: Barry Lyu, the GOAT

  Writes an SPI formatted message to the USB port for the SPI Driver. Requires that src_msg 
  is a 24 bit message. Use spi_stream_protocol.py to format these messages.
  """
  src_msg_bytes = []

  while src_msg.nbits > 8:
    src_msg_bytes.append(int(src_msg[src_msg.nbits - 8 : src_msg.nbits]))
    src_msg = src_msg[: src_msg.nbits - 8]
  src_msg_bytes.append(int(src_msg))
  device.sel()

  readbytes = device.writeread(src_msg_bytes)

  device.unsel()

  return Bits40(int.from_bytes(readbytes, "big") >> 2)

