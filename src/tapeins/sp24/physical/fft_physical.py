# import numpy as plt
import serial
import cli_spi_physical as csp

import math


def set_serial(comport, baudrate):
    ser = serial.Serial(
        comport, baudrate, timeout=0.1
    )  # 1/timeout is the frequency at which the port is read

    return ser


def readserial(ser):
    data = ser.readline().decode().strip()

    if data:
        # print(data)
        data = data[data.index(": ") + 2 :]
        data = data.split(" ")
        print(f"{data[0]}, {data[1]}")
        print(csp.inject(int(data[1])))


def readserial_fft(comport, baudrate):

    ser = serial.Serial(
        comport, baudrate, timeout=0.1
    )  # 1/timeout is the frequency at which the port is read

    while True:
        data = ser.readline().decode().strip()

        if data:
            # print(data)
            data = data[data.index(": ") + 2 :]
            data = data.split(" ")
            print(f"{data[0]}, {data[1]}")
            print(csp.fft_inj(int(data[1])))


def test_loopback():
    csp.config(0x10000)
    while True:
        val = csp.inject(0x01234)
        print(val)


def config_fft():
    csp.config(0x10002)
    csp.config(0x30008)


def gen_wave(numpts, freq, amp, offset):
    assert amp <= 1 and amp >= 0

    list = []

    for i in range(numpts):
        list.append(65535*amp*math.sin(freq*i/40000000) + offset)
    
    return list


x = []
y = []

if __name__ == "__main__":
    config_fft()


    
    while True:
        packet = gen_wave(32, 1000000, 0.5, 1000)
        print(packet)
        csp.fft_inj(packet)

    # readserial("/dev/ttyACM0", 115200)
    # readserial("COM18", 115200)
    
