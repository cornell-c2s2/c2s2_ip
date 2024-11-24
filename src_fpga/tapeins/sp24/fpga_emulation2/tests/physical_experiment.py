#!/home/c2/c2s2-toolchain/toolchain-build/software/Python/3.11.5-GCCcore-13.2.0/bin/python

import os
from spi_driver_physical import *


if __name__ == "__main__":
    for i in range(5):
        spi_reset_a()
        os.system(
            f"pytest /home/c2/c2s2_ip/src_fpga/tapeins/sp24/fpga_emulation2/tests/test_interconnect_physical.py -v -k test_loopback > out_rst_5s_lb{i+1}.txt"
        )
