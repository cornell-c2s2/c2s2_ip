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
data_recv = np.array([]).astype(np.int32)  # for messages received from the chip


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
    raise Exception(f"Out of bounds numerical value; cannot send {val} to chip.")

import pdb
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
    # pdb.set_trac/e()
    raise Exception(f"Out of bounds numerical value; cannot send {val} to chip.")
  

def gen_fft(index, mag):
  # msgs = np.ones(16).astype(np.uint16) * 0xfffe
  # # msgs[index] += mag
  # msgs = np.array([0xfc33,
  #   0xfc33,
  #   0x01e2,
  #   0x0026,
  #   0x006d,
  #   0x000c,
  #   0xffc6,
  #   0xffc4,
  #   0x001e,
  #   0xfff6,
  #   0xffda,
  #   0xff71,
  #   0x0013,
  #   0x001a,
  #   0x003c,
  #   0x0042])
  msgs = np.ones(16) * 0x7fff
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
    spi_write_read_print(Config.CLS_CUTOFF_FREQ + 0)
    spi_write_read_print(Config.CLS_CUTOFF_MAG + 0x8000)
    spi_write_read_print(Config.CLS_SAMP_FREQ + 44100)


    i = 0
    mag = 0x6400

    for i in range(3):
      array = gen_fft(i, mag)
      # print("\nNEW TRANSACTION\n")
      for k in range(16):
        send, recv = spi_write_read_print(np.uint32(array[k]) + 0x20000)
        data_recv = np.concatenate((data_recv, np.array([recv])))
      spi_read_print()


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
    with open("data_recv3.txt", "w") as f:
      for msg in data_recv:
        f.write(str(fft(msg)) + "\n")
        # f.write(str(msg) + "\n")

    # Save recorded audio to a .wav file
    # output_filename = "recorded_audio.wav"
    # wf = wave.open(output_filename, 'wb')
    # wf.setnchannels(CHANNELS)
    # wf.setsampwidth(p.get_sample_size(FORMAT))
    # wf.setframerate(RATE)
    # wf.writeframes(b''.join(audio_bytes))
    # wf.close()

    # print(f"Audio saved to '{output_filename}'")

