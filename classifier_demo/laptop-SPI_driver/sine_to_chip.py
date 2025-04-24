import numpy as np
from cli_interface import *
import matplotlib.pyplot as plt
import pymtl3

# sampling rate
sr = 32

# sampling interval
ts = 1.0/sr
t = np.arange(0,1,ts)
freq = 0.5
x = 3*np.sin(2*np.pi*freq*t)

# freq = 4
# x += np.sin(2*np.pi*freq*t)
# freq = 7
# x += 0.5* np.sin(2*np.pi*freq*t)

# print(len(x))
# plt.figure(figsize = (8, 6))
# plt.plot(t, x, ‘r’)
# plt.ylabel(‘Amplitude’)
# plt.show()

if __name__ == "__main__":
  port1 = "COM7"
  # port2 = "COM18"

  # # Initialize the USB port to COM7, and set the print mode to print out classifier messages
  init_usb(port1)
  show_device_info()
  set_print_mode(1)

  # Configure the chip for information from SPI, to FFT, to classifier, to SPI output
  spi_write_read(Config.INXBAR_SPI_FFT)
  spi_write_read(Config.CLSXBAR_FFT_SPI)
  # spi_write_read(Config.OUTXBAR_CLS_SPI)

  # Set up the serial monitor
  # ser = serial.Serial(
  #   port2, 115200, timeout=0.1
  # )  # 1/timeout is the frequency at which the port is read

  for val in x:
    # print((val*2048))
    spi_write_read(0x00000 + int(mk_bits(32)(val*2048)[:16]))
    # spi_write_read(0x00018)
  for i in range(16):
    spi_read()
  # start = time.time()
  # end = 0.0

  # sampling_freq = 882
  # playback_freq = 44100

  # sampling_period = 1.0 / sampling_freq

  # size = 3

  # data = np.zeros(size*sampling_freq)
  # i = 0

  # end = time.time_ns()
  # for i in range(size*sampling_freq):
  #   # print("new iteration")
  #   start = time.time_ns()
  #   data[i] = readserial(ser)
  #   while (end-start < sampling_period):
  #     end = time.time_ns()

  # audio = np.zeros(size*playback_freq).astype(np.int16)

  # j = 0
  # for i in range(size*sampling_freq):
  #   for j in range(50):
  #     audio[j+i*50] = int(data[i])
  
  
  # with wave.open("output.wav", "w") as wav_file:
  #   wav_file.setnchannels(1)
  #   wav_file.setsampwidth(2)
  #   wav_file.setframerate(playback_freq)
  #   wav_file.writeframes(audio.tobytes())

  # for i in range(data.shape[0]):
  #   print(data[i])
  # print("success!")

  # Send data to chip
  # beg = time.time()
  # i = 10000
  # data = np.zeros(i)
  # while (i > 0):
  #   data[10000-i] = readserial(ser)
  #   i -= 1

  #   # if end - start >= sampling_period:
  #   #   start = time.time()
  #   #   data[i] = readserial(ser)
  #   #   i += 1

  # fin = time.time()
  # print("Func is ", fin-beg)

  # if (i+1==size):
  #       with wave.open("output.wav", "w") as wav_file:
  #         wav_file.setnchannels(1)
  #         wav_file.setsampwidth(2)
  #         wav_file.setframerate(sampling_freq)
  #         wav_file.writeframes(data.tobytes())

      

    # data = readserial(ser)
    # if data > max:
    #   max = data
    #   print(max)

    # spi_write_read(0x00000) # This is dummy data
    # spi_write_read(0x08000)
    # spi_write_read(0x0ffff)
    # spi_write_read(0x07fff)