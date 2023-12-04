import pytest
import struct
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib import stream
from src.floating_point.HardFloat.pyMTL_harness.hardfloatmult32 import mulRecFN


# def test_force_fail(cmdline_opts):
#     run_test_vector_sim(
#         mulRecFN(8, 23),  # dut
#         [("a b out* exceptionFlags* control roundingMode"), *[[Bits32(0), Bits32(0), Bits32(1), Bits5(0), Bits1(1), Bits3(0)]]],  # test cases
#         cmdline_opts,
#     )


# def test_testfloat_fail0(cmdline_opts):
#     run_test_vector_sim(
#         mulRecFN(8, 23),  # dut
#         [("a b out* exceptionFlags* control roundingMode"), *[[Bits32(0xce9b00b3), Bits32(0x3cbf2e43), Bits32(0xCBE78310), Bits5(1), Bits1(1), Bits3(0)]]],  # test cases
#         cmdline_opts,
#     )

# def test_testfloat_fail1(cmdline_opts):
#     run_test_vector_sim(
#         mulRecFN(8, 23),  # dut
#         [("a b out* exceptionFlags* control roundingMode"), *[[Bits32(0x3d0400ff), Bits32(0xbf010ffe), Bits32(0xBC85197F), Bits5(1), Bits1(1), Bits3(0)]]],  # test cases
#         cmdline_opts,
#     )

# def test_testfloat_fail2(cmdline_opts):
#     run_test_vector_sim(
#         mulRecFN(8, 23),  # dut
#         [("a b out* exceptionFlags* control roundingMode"), *[[Bits32(0x8683f7ff), Bits32(0xc07f3fff), Bits32(0x7839504), Bits5(1), Bits1(1), Bits3(0)]]],  # test cases
#         cmdline_opts,
#     )
# http://www.jhauser.us/arithmetic/TestFloat-3/doc/testfloat_gen.html
@pytest.mark.slow
def test_with_testfloat(testfloat_gen, cmdline_opts):
    # Generate 100,000 test cases from testfloat.
    testfloat_data = testfloat_gen("f32_mul", level=2, n=100000, extra_args="-tininessafter -rnear_even")

    # Truncate the error flags here because we don't want them.
    # testfloat_data = [test_case[0:3] for test_case in testfloat_data]
    for test_case in testfloat_data:
        test_case.append(Bits1(1)) # control bit 1=tininessafter
        test_case.append(Bits3(0)) # rounding mode 0=rnear even

    run_test_vector_sim(
        mulRecFN(8, 23),  # dut
        [("a b out* exceptionFlags* control roundingMode"), *testfloat_data],  # test cases
        cmdline_opts,
    )

    # print(testfloat_data)
