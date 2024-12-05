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
- Running tests

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

Once you know the port name, open up `tests/spi_driver_physical.py.physical` in the repo and replace
`
s = SPIDriver("/dev/ttyUSB0")
`
with
`
s = SPIDriver(<path to the port>)
`

#### A.3. Putting Chip On Caravel Board
Now we have to put the chip on the caravel board. Use one of the black boards. **Leave the board unplugged!**

The chip on the board should be the C3 chip, to identify it, squint real hard at the black square packaging on the chip and observe that the faint text on it starts with C3. If its not C3, or if the board doesn't have a chip on it, take out a C3 chip, then plug and screw in the chip (just to keep it in place, don't screw it too tight as it will damage the PCB)

**DO NOT PLUG/UNPLUG THE CHIP WHILE THE BOARD IS POWERED!**

#### A.4. Connecting SPI Driver and board
Now we have to connect the SPI and the Caravel board. There are 5 pins that you need to connect:

| SPI Driver Pin  | Caravel Board Pin |
| -------------   | -------------     |
| sck             | IO[9]             |
| miso            | IO[10]            |
| mosi            | IO[8]             |
| cs              | IO[7]             |
| GND             | GND               | 

There are several pins labeled as GND on the Caravel board, use the one that is in the column of gpio (the one directly above vdda1 and IO[0]).

After you plugin the GND pin, the power indicator LED might light up faintly because its being semi-powered by the GPIOs.

#### A.5. Connecting the Caravel Board
Finally, you can plug the Caravel Board to the computer with another micro-usb cable. Observe that the power indicator LED becomes fully on and is brighter than it was in A.4.

### B. Flashing The Caravel Board

Now we need to flash the board.

Clone the [c2s2_firmware](https://github.com/cornell-c2s2/c2s2_firmware) repo if you haven't already.

cd into `c2s2_firmware/firmware/24tapeout`.

run `make clean flash` (if you don't have riscv-gnu-toolchain installed, just run `make flash`).

Let it run to completion, if it didn't throw errors, observe that the D3 LED on the Caravel board is blinking.

### C. Running Tests

To run the physical tests, first rename `tests/spi_driver_physical.py.physical` to `tests/spi_driver_physical.py`, and `tests/test_interconnect_physical.py.physical` to `tests/test_interconnect_physical.py`.

Then run `pytest test/test_interconnect_physical.py`

Voila! You should see tests passing if it was setup correcly. Occasionally a single test may fail, and maybe bring down all tests after it as well. This is likely due to unstable wire connections and should resolve itself with another run.
