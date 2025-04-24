"""
A simple python file that sends microphone data into the digital chip through the SPI Driver

Authors: Simeon Turner, Nathan Rakhlin
"""


from cli_interface import *
import time

import numpy as np


if __name__ == "__main__":
  port1 = "COM7"

  # Initialize the USB port to COM7, and set the print mode to print out classifier messages
  init_usb(port1)
  show_device_info()
  set_print_mode(1)

  # Configure the chip for information from SPI, to FFT, to classifier, to SPI output
  spi_write_read(Config.INXBAR_SPI_SPI)
  # spi_write_read(Config.CLSXBAR_FFT_SPI)
  # spi_write_read(Config.OUTXBAR_CLS_SPI)

  i=0
  send = []
  recv = []

  start = time.time()
  try:
    while (1):
      sent, recvd = spi_write_read(0xdead)
    
      send.append(sent)
      recv.append(recvd)

      i += 1

  except KeyboardInterrupt:
    end = time.time()
    print("Stopping.")
    print("\nExchange rate is: ", 1/((end-start)/i), "Hz")
  
  finally:
    # print(send)
    # print()
    # print(recv)
    pass