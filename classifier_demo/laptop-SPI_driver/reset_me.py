import cli_interface as cli

# if __name__ == "__main__":
cli.init_usb('COM7')
cli.spi_trigger_a(0.1)