"""
Sends microphone data into the digital chip through the SPI Driver

Authors: Simeon Turner, Nathan Rakhlin
"""


import numpy as np
import wave
import pyaudio
from cli_interface import *


# Audio config
SAMPLE_RATE = 500
CHUNK_DURATION = 1.0 / SAMPLE_RATE  # in seconds
RATE = 44100  # in samples per second
CHUNK_SIZE = int(RATE * CHUNK_DURATION)  # samples per chunk
FORMAT = pyaudio.paInt16
CHANNELS = 1

# Open stream for microphone input
p = pyaudio.PyAudio()
stream = p.open(format=FORMAT,
                channels=CHANNELS,
                rate=RATE,
                input=True,
                frames_per_buffer=CHUNK_SIZE)

# Arrays and lists for data collection
audio_bytes = [] # for raw audio data
audio_vals = np.array([]).astype(np.int32) # for numerically valued audio data
data_recv = np.array([]).astype(np.int32)  # for messages received from the chip


# Function for sign extension
def sext_int16(val):
  """
  Returns the correctly sign extended version of the value
  """
  # temp = val.astype(np.int32)
  print(hex(val.astype(np.uint16)))
  return val
  # if val >= 0 and val <= 32767:
  #   return (val).astype(np.int16)
  # elif val < 0 and val >= -32768:
  #   return (val + 65536).astype(np.int16)
  # else:
  #   raise Exception("Out of bounds numerical value; cannot send to chip.")


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
  

def big_to_little(data):
    samples = np.frombuffer(data, dtype='>i2')  # big-endian 16-bit signed int
    return samples.astype('<i2').tobytes()      # convert to little-endian


if __name__ == "__main__":
  spi_port = "COM7"

  # Stage 1: collecting audio data
  try:
    print("\nRECORDING FROM MICROPHONE")
    print("Press Ctrl+C to finish recording.\n")

    valid_data = False
    while (not valid_data):
      # Read audio data from chunk
      data = stream.read(CHUNK_SIZE, exception_on_overflow=False)
      # Determine if there is valid audio data in this chunk
      val_chunk = data.hex()
      i = 0
      while i+4 <= len(val_chunk):
        val = val_chunk[i:i+4]
        if not (val[0] == "0" or val[0] == "f"):
          valid_data = True # break loop if there is valid audio data
        i += 4

    while (1):
      # Read audio data from chunk
      data = stream.read(CHUNK_SIZE, exception_on_overflow=False)
      audio_bytes.append(data)
    
      # Convert bytes to numpy array
      # sample = np.frombuffer(data, dtype='>i2')
      sample = np.frombuffer(data, dtype=np.int16)
      q88 = (sample)

      for i in range(q88.shape[0]):
        if q88[i] > 32767 or q88[i] < -32768:
          raise Exception("Value is " + str(q88[i]))
        
      audio_vals = np.concatenate((audio_vals, q88))


  # Stage 2: sending audio data to the chip
  except KeyboardInterrupt:
    print("\nTRANSFERRING DATA TO CHIP")
    print("Press Ctrl+C to interrupt the transfer process.\n")

    try:
      # Initialize the USB port to COM7, and set the print mode to print out classifier messages
      init_usb(spi_port)
      set_print_mode(1)

      # Configure the chip for information from SPI, to FFT, to classifier, to SPI output
      spi_write_read(Config.INXBAR_SPI_FFT)
      spi_write_read(Config.CLSXBAR_FFT_SPI)
      # spi_write_read(Config.OUTXBAR_CLS_SPI)
      # time.sleep(1)
      # set_print_mode(1)
      spi_write_read_print(Config.CLS_CUTOFF_FREQ + 0)
      spi_write_read_print(Config.CLS_CUTOFF_MAG + 0xff70)
      spi_write_read_print(Config.CLS_SAMP_FREQ + 44100)
      # time.sleep(5)
      # set_print_mode(2)

      # Send the recorded audio
      for i in range(audio_vals.shape[0]):
        send, recv = spi_write_read_print(audio_vals[i].astype('<i2').astype(np.uint16))
        data_recv = np.concatenate((data_recv, np.array([recv])))

    except KeyboardInterrupt:
      print("Interrupting chip data transfer process...")
  

  # Stage 3: saving transfer data
  finally:
    print("\nSAVING AUDIO AND TRANSFER DATA\n")
    stream.stop_stream()
    stream.close()
    p.terminate()

    with open("audio_bytes.txt", "w") as f:
      for chunk in audio_bytes:
        i = 0
        val = chunk.hex()
        while i+4 <= len(val):
          f.write(val[i:i+4] + "\n")
          i += 4

    with open("audio_vals.txt", "w") as f:
      for val in audio_vals:
        f.write(str(hex(val.astype('<i2'))) + "\n")
        # str(int(hex(val), 16) / 256) + "   |   " + 

    with open("data_recv.txt", "w") as f:
      for msg in data_recv:
        # f.write(str(fft(msg)) + "\n")
        f.write(str(msg[:20]) + "\n")

    # Save recorded audio to a .wav file
    output_filename = "recorded_audio.wav"
    wf = wave.open(output_filename, 'wb')
    wf.setnchannels(CHANNELS)
    wf.setsampwidth(p.get_sample_size(FORMAT))
    wf.setframerate(RATE)
    wf.writeframes(b''.join(audio_bytes))
    wf.close()

    print(f"Audio saved to '{output_filename}'")

