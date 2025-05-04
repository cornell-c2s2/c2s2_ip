"""
A simple python file that sends microphone data into the digital chip through the SPI Driver

Authors: Simeon Turner, Nathan Rakhlin
"""


from cli_interface import *
import time

import numpy as np
import wave
import pyaudio


# Audio config
SAMPLE_RATE = 500
CHUNK_DURATION = 1.0 / SAMPLE_RATE  # seconds
RATE = 44100  # samples per second
CHUNK_SIZE = int(RATE * CHUNK_DURATION)  # samples per chunk
FORMAT = pyaudio.paInt16
CHANNELS = 1

# Open stream for microphone input
stream = p.open(format=FORMAT,
                channels=CHANNELS,
                rate=RATE,
                input=True,
                frames_per_buffer=CHUNK_SIZE)


def sext_int16(val):
  if val >= 0 and val <= 32767:
    return val
  elif val < 0 and val >= -32768:
    return val + 65536
  else:
    raise Exception("Out of bounds numerical value; cannot send to chip.")
  

def gen_sine(freq, duration):
  sr = 44100 # sampling rate
  ts = 1.0/sr # sampling interval
  t = np.arange(0,duration,ts)
  return 3*np.sin(2*np.pi*freq*t)


if __name__ == "__main__":
  port1 = "COM7"

  i=0
  print("Sampling audio at 44.1 kHz... Press Ctrl+C to finish sampling and send audio data to chip.")
  try:
    valid_data = False

    while (1):
      # Read audio chunk
      data = stream.read(CHUNK_SIZE, exception_on_overflow=False)
      audio_bytes.append(data)  # Save raw audio data
    
      # Convert bytes to numpy array
      sample = np.frombuffer(data, dtype=np.int16)
      q88 = (sample * 256).astype(np.int16)
      for i in range(q88.shape[0]):
        if q88[i] > 32767 or q88[i] < -32768:
          raise Exception("Value is " + str(q88[i]))
      audio_vals = np.concatenate((audio_vals, q88))


  except KeyboardInterrupt:
    try:
      print("\nSending audio data to chip.")

      # Initialize the USB port to COM7, and set the print mode to print out classifier messages
      init_usb(port1)
      show_device_info()
      set_print_mode(1)

      # Configure the chip for information from SPI, to FFT, to classifier, to SPI output
      spi_write_read_print(Config.INXBAR_SPI_FFT)
      spi_write_read_print(Config.CLSXBAR_FFT_SPI)
      # spi_write_read_print(Config.OUTXBAR_CLS_SPI)

      for i in range(audio_vals.shape[0]):
        send, recv = spi_write_read_print(sext_int16(audio_vals[i]))
        # send, recv = spi_write_read_print(audio_vals[i])
        data_recv = np.concatenate((data_recv, np.array([recv])))
    except KeyboardInterrupt:
      print("Interrupting chip data transfer process...")
  
  finally:
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
        f.write(str(val) + "    |    " + str(hex(val)) + "\n")
    with open("data_recv.txt", "w") as f:
      for msg in data_recv:
        f.write(str(msg) + "\n")

    # Save recorded audio to a .wav file
    output_filename = "recorded_audio.wav"
    wf = wave.open(output_filename, 'wb')
    wf.setnchannels(CHANNELS)
    wf.setsampwidth(p.get_sample_size(FORMAT))
    wf.setframerate(RATE)
    wf.writeframes(b''.join(audio_bytes))
    wf.close()

    print(f"Audio saved to '{output_filename}'")