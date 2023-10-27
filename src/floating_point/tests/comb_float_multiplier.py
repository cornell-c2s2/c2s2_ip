import pytest
import random
import struct
import os
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib.test_utils import mk_test_case_table
from pymtl3.stdlib import stream
from src.floating_point.harnesses.comb_float_multiplier import CombFloatMultiplierWrapper


# Creates a test harness class for the `CombFloatMultiplier` module.
class Harness(Component):
    def construct(s, harness):
        s.harness = harness

        s.src0 = stream.SourceRTL(mk_bits(32))
        s.src1 = stream.SourceRTL(mk_bits(32))
        s.sink = stream.SinkRTL(mk_bits(32))

        # bind the harness to the dut (that is within the wrapper)!
        s.src0.send //= s.harness.in0
        s.src1.send //= s.harness.in1
        s.harness.out //= s.sink.recv

    def done(s):
        return s.src0.done() and s.src1.done() and s.sink.done()


# Initialize a simulatable model
def create_model():
    model = CombFloatMultiplierWrapper()

    # Create a harness wrapping our `CombFloatMultiplier` module.
    return Harness(model)


def f32_as_int(x):
    bytes = struct.pack(">f", x)
    return int.from_bytes(bytes, byteorder="big")


def int_as_f32(x):
    bytes = x.to_bytes(length=4, byteorder="big")
    return struct.unpack(">f", bytes)[0]


test_case_table = mk_test_case_table([

    (        "in0             in1             out"),
    ["basic", int_as_f32(1),  int_as_f32(1),  int_as_f32(1) ]
])

# Pull test cases from berkeley testfloat generator (piped through fifo)
# This function outputs an array of lines from the testfloat generator
def read_testfloat_fifo_until_empty(fifo_path):

    try:
        fifo_fd = os.open(fifo_path, os.O_RDONLY)

        lines = []

        while True:
            line = b""
            while True:
                try:
                    byte = os.read(fifo_fd, 1)
                    if not byte:
                        break  # No more data in the FIFO
                    line += byte

                    if byte == b'\n':
                        break  # Stop reading when a newline is encountered
                except BlockingIOError:
                    break  # No more data available to read

            if not line:
                break  # No more lines in the FIFO
            lines.append(line)

        os.close(fifo_fd)
        return lines
    except FileNotFoundError:
        print(f"Named pipe '{fifo_path}' not found.")
        return None

# This function takes an array of lines and outputs a test_array
def berkeley_testfloat_to_testarray(data_array):
    test_array = [("in0 in1 out")]
    for line in data_array:
        line_split = line.split() 

        in0 = int(line_split[0], 16)
        in1 = int(line_split[1], 16)
        out = int(line_split[2], 16)

        test_array.append([in0, in1, out])
    return test_array

# @pytest.mark.parametrize( **test_case_table )
def test_simple():
    # Create our model.
    model = create_model()
    
    run_test_vector_sim(
        CombFloatMultiplierWrapper(32, 23, 8), # dut
        [("in0 in1 out"),[int_as_f32(3),  int_as_f32(2),  int_as_f32(6)]], # test cases
        cmdline_opts={},
    )

# note: this test requires that the test cases have already been piped to the test_fifo
# using the testfloat_gen() function
# http://www.jhauser.us/arithmetic/TestFloat-3/doc/testfloat_gen.html
def test_with_berkeley_library():
    FIFO = '../src/floating_point/tests/test_fifo'

    # Create our model.
    model = create_model()

    # data_array = read_testfloat_fifo_until_empty(FIFO)
    test_array = berkeley_testfloat_to_testarray(read_testfloat_fifo_until_empty(FIFO))

    run_test_vector_sim(
        CombFloatMultiplierWrapper(32, 23, 8), # dut
        test_array, # test cases
        cmdline_opts={},
    )

    # model.set_param(
    #     "top.src0.contruct",
    #     msgs=[int_as_f32(1)],
    #     initial_delay=0,
    #     interval_delay=0,
    # )

    # model.set_param(
    #     "top.src1.construct",
    #     # Input values to stream through the block in order
    #     msgs=[int_as_f32(1)],
    #     # Cycles to wait after reset before starting to send inputs
    #     initial_delay=0,
    #     # Cycles to wait before sending next input (before `send_val` set high)
    #     interval_delay=0,
    # )

    # model.set_param(
    #     "top.sink.construct",
    #     # Expected output values to read from the block in order
    #     msgs=[int_as_f32(1)],
    #     # Cycles to wait after reset before setting `recv_rdy` to high
    #     initial_delay=0,
    #     # Cycles to wait between outputs before setting `recv_rdy` to high
    #     interval_delay=0,
    # )

    # run_sim(
    #     model,
    #     cmdline_opts={
    #         "dump_textwave": False,
    #         # Creates the vcd file test_simple_<bitwidth>.vcd for debugging.
    #         "dump_vcd": f"basic test",
    #         # Optional, used to test accurate cycle counts.
    #         "max_cycles": None,
    #     },
    # )

    
    

