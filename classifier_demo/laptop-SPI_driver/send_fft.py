"""
Sends microphone data into the digital chip through the SPI Driver

Authors: Simeon Turner, Nathan Rakhlin
"""


import numpy as np
import wave
from cli_interface import *

# Arrays and lists for data collection
audio_bytes = [] # for raw audio data
audio_vals = np.array([]).astype(np.int32) # for numerically valued audio data
data_recv2 = np.array([]).astype(np.int32)  # for messages received from the chip


# Function for sign extension
def sext_int16(val):
  """
  Returns the correctly sign extended version of the value
  """
  if val >= 0 and val <= 32767:
    return val
  elif val < 0 and val >= -32768:
    return val + 65536
  else:
    raise Exception("Out of bounds numerical value; cannot send to chip.")


def fft(msg):
  """
  Returns the numerical value of the hex message received from the FFT
  """
  val = int(msg[:16])

  if val >= 0 and val <= 32767:
    return val / 256
  elif val > 32767 and val <= 65536:
    return (val - 65536) / 256
  else:
    raise Exception("Out of bounds numerical value; cannot send to chip.")
  

def gen_fft(index, mag):
  msgs = np.zeros(16)
  msgs[index] += mag
  return msgs


if __name__ == "__main__":
  spi_port = "COM7"

  try:
    # Initialize the USB port to COM7, and set the print mode to print out classifier messages
    init_usb(spi_port)
    set_print_mode(2)

    # Configure the chip for information from SPI, to FFT, to classifier, to SPI output
    # spi_write_read(Config.INXBAR_SPI_SPI)
    spi_write_read(Config.CLSXBAR_SPI_CLS)
    spi_write_read(Config.OUTXBAR_CLS_SPI)
    # set_print_mode(1)
    spi_write_read_print(Config.CLS_CUTOFF_FREQ + 1300)
    spi_write_read_print(Config.CLS_CUTOFF_MAG + 0x5000)
    spi_write_read_print(Config.CLS_SAMP_FREQ + 44100)


    i = 0
    mag = 0x6400

    with open("data_recv.txt", "r") as  f:
      lines = f.readlines()
    lines.pop()
    while(1):
      send, recv = spi_write_read_print(np.uint32(int(lines[i][:5], 16)))
      data_recv2 = np.concatenate((data_recv2, np.array([recv])))
      i += 1


  # Stage 2: sending audio data to the chip
  except KeyboardInterrupt:
    print("Interrupting chip data transfer process...")
  

  # Stage 3: saving transfer data
  finally:
    print("\nSAVING AUDIO AND TRANSFER DATA\n")
    # stream.stop_stream()
    # stream.close()
    # p.terminate()

    # with open("audio_bytes.txt", "w") as f:
    #   for chunk in audio_bytes:
    #     i = 0
    #     val = chunk.hex()
    #     while i+4 <= len(val):
    #       f.write(val[i:i+4] + "\n")
    #       i += 4
    # with open("audio_vals.txt", "w") as f:
    #   for val in audio_vals:
    #     f.write(str(val / 256))
    with open("data_recv2.txt", "w") as f:
      for msg in data_recv2:
        f.write(str(msg) + "\n")
        # f.write(str(msg) + "\n")


