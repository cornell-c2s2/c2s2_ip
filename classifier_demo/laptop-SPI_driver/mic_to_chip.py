"""
A simple python file that sends microphone data into the digital chip through the SPI Driver

Authors: Simeon Turner, Nathan Rakhlin
"""


from cli_interface import *
import serial


def readserial(ser):  
  data = ser.readline().decode().strip()

  if data:
    # print(data)
    data = data[data.index(": ") + 2 :]
    data = data.split(" ")
    print(data)
    return data[1]


if __name__ == "__main__":
  port = "COM7"

  # Initialize the USB port to COM7, and set the print mode to print out classifier messages
  init_usb(port)
  show_device_info()
  set_print_mode(2)

  # Configure the chip for information from SPI, to FFT, to classifier, to SPI output
  # spi_write_read(Config.INXBAR_SPI_FFT)
  # spi_write_read(Config.CLSXBAR_FFT_CLS)
  # spi_write_read(Config.OUTXBAR_CLS_SPI)

  # Set up the serial monitor
  ser = serial.Serial(
    port, 115200, timeout=0.1
  )  # 1/timeout is the frequency at which the port is read

  # Send data to chip
  while (1):
    # spi_write_read(readserial(ser))
    print("readserial printed: ", readserial(ser))

    # spi_write_read(0x00000) # This is dummy data
    # spi_write_read(0x08000)
    # spi_write_read(0x0ffff)
    # spi_write_read(0x07fff)