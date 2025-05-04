"""
Sends microphone data into the digital chip through the SPI Driver

Authors: Simeon Turner, Nathan Rakhlin
"""


import numpy as np
from spi_interface import *


PRINT_MODE = 1
FFT_MAG = 0xffff

CUTOFF_FREQ = 0
CUTOFF_MAG = 0xfffe
SAMP_FREQ = 44100


# Arrays and lists for data collection
audio_bytes = [] # for raw audio data
audio_vals = np.array([]).astype(np.int32) # for numerically valued audio data
data_recv = np.array([]).astype(np.int32)  # for messages received from the chip
  

def gen_fft(index, mag):
  msgs = np.ones(16)
  msgs[index] = mag
  return msgs


if __name__ == "__main__":
  spi_port = "COM7"

  print("\n+ + + RUNNING TEST IDEAL + + +\n")

  try:
    # Initialize the USB port to COM7, and set the print mode to print out classifier messages
    init_usb(spi_port)
    set_print_mode(PRINT_MODE)

    # Configure the chip for information from SPI, to FFT, to classifier, to SPI output
    # spi_write_read(Config.INXBAR_SPI_SPI)
    spi_write_read_print(Config.CLSXBAR_SPI_CLS)
    spi_write_read_print(Config.OUTXBAR_CLS_SPI)
    # set_print_mode(1)
    spi_write_read_print(Config.CLS_CUTOFF_FREQ + CUTOFF_FREQ)
    spi_write_read_print(Config.CLS_CUTOFF_MAG + CUTOFF_MAG)
    spi_write_read_print(Config.CLS_SAMP_FREQ + SAMP_FREQ)


    i = 0

    for i in range(16):
      array = gen_fft(i, FFT_MAG)

      # print("\nNEW TRANSACTION\n")

      for k in range(16):
        send, recv = spi_write_read_print(np.uint32(array[k]) + 0x20000)
        # data_recv = np.concatenate((data_recv, np.array([recv])))
      spi_read_print()
    
    print("\n")


  # Stage 2: sending audio data to the chip
  except KeyboardInterrupt:
    print("Interrupting chip data transfer process...")

