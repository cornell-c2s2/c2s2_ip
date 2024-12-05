# SP24 Digital Tapeout

> This folder contains the simulation and physical tests for the sp24 tapeout/tape-in2.

## Simulation

Running the following command in this directory runs all the tests in RTL simulation through pymtl and pytest:

`pytest tests/test_interconnect.py`

## FPGA Testing

> In the works, will be added soon.

## Tapeout Testing

For tapeout testing, there are three main steps:
- Connecting devices
- Flashing the caravel board
- Running the tests

### A. Connecting Devices

We need four devices for the tests:
- An SPI Driver
- A Caravel board
- A digital chip packaged in m.2 slots
- Either the C2 workstation or a separate computer

#### A.1. Setup software on the computer
Below is the testing enviroment already setup C2. Jump to A.2 if you are using C2. 
For your own computer you have to install these packages:
```
python 3.11.5
pytest 8.0.1
pymtl3 3.1.16
pyftdi 0.55.4
spidriver 1.1.1
```
After you install them, try running the RTL simulation with pytest and observe that all tests pass.
Otherwise install other required packages accordingly.

> The compilation of the flashing code requires [riscv-gnu-toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain.git) to be installed.
> You can follow the instructions in the official repository to install it on your computer. Since installing it is much a hassle,
> the compiled programs are uploaded to this repo. Just flashing the board with the precompiled board does not require the toolchain.

#### A.2. SPI Driver
Connect an SPI Driver to the computer with the micro-usb cable. Its LED should lightup and display the pin names.

We then need to identify the port name of SPI-driver on the computer.

  - For Linux: run `ls -l /dev | grep "USB"`, you should be presented with a list of devices with names like `ttyUSB0`, 
pick the device which has a timestamp that matches the time when you plugged the SPI Driver in. Your path to the port should look like `/dev/ttyUSBX`.

  - For Windows: it most likely looks something vaguely like `.//ROM3`, look up on locating peripheral port for windows.

  - For MacOS: Haven't tested. Probably similar to Linux.

You'll also have to change the permissions of the port (probably requires sudo access):
`
sudo chmod 666 <path to the port>
`

Once you know the port name, open up `spi_driver_physical.py` in the repo and replace
`
s = SPIDriver("/dev/ttyUSB0")
`
with
`
s = SPIDriver(<path to the port>)
`

### A.3 The Caravel Board
Now we have to connect the caravel board. Your best bet is one of the black boards.

The chip on the board should be the `C3` chip, to identify it, squint real hard at the black square packaging on the chip and observe that the faint text on it starts with `C3`


> TO BE CONTINUED... WORK IN PROGRESS
