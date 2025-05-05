from spi_interface import *


def set_for_test(usb):
  init_usb(usb)
  spi_trigger_a(0.05)