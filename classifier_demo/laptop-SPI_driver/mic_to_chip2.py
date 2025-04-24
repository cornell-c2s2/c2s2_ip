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
SAMPLE_RATE = 3200
CHUNK_DURATION = 1.0 / SAMPLE_RATE  # seconds
RATE = 44100  # samples per second
CHUNK_SIZE = int(RATE * CHUNK_DURATION)  # samples per chunk
FORMAT = pyaudio.paInt16
CHANNELS = 1

# Start PyAudio
p = pyaudio.PyAudio()
audio_bytes = []
audio_vals = np.array([]).astype(np.float32)
data_recv = np.array([]).astype(np.int32)

# Open stream for microphone input
stream = p.open(format=FORMAT,
                channels=CHANNELS,
                rate=RATE,
                input=True,
                frames_per_buffer=CHUNK_SIZE)


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
  print("Sampling audio at 44.1 kHz... Press Ctrl+C to finish sampling and send audio data to chip.")
  try:
    while (1):
      # Read audio chunk
      data = stream.read(CHUNK_SIZE, exception_on_overflow=False)
      audio_bytes.append(data)  # Save raw audio data
    
      # Convert bytes to numpy array
      sample = np.frombuffer(data, dtype=np.float16)
      audio_vals = np.concatenate((audio_vals, sample))


  except KeyboardInterrupt:
    try:
      print("\nSending audio data to chip.")

      for i in range(audio_vals.shape[0]):
        send, recv = spi_write_read(audio_vals[i])
        data_recv = np.concatenate((data_recv, np.array([recv])))
    except KeyboardInterrupt:
      print("Interrupting chip data transfer process...")
  
  finally:
    stream.stop_stream()
    stream.close()
    p.terminate()

    np.savetxt("audio_bytes.csv", audio_bytes, delimiter=',')
    np.savetxt("audio_vals.csv", audio_vals, delimiter=',')
    np.savetxt("data_recv.csv", data_recv, delimiter=',')

    # Save recorded audio to a .wav file
    output_filename = "recorded_audio.wav"
    wf = wave.open(output_filename, 'wb')
    wf.setnchannels(CHANNELS)
    wf.setsampwidth(p.get_sample_size(FORMAT))
    wf.setframerate(RATE)
    wf.writeframes(b''.join(audio_bytes))
    wf.close()

    print(f"Audio saved to '{output_filename}'")