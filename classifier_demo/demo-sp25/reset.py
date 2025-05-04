import spi_interface as spi

spi.init_usb('COM7')
spi.spi_trigger_a(0.1)