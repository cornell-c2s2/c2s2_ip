import pytest
import struct
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib import stream
from src.floating_point.HardFloat.pyMTL_harness.hardfloatadd32 import addRecFN

# http://www.jhauser.us/arithmetic/TestFloat-3/doc/testfloat_gen.html
@pytest.mark.slow
def test_with_testfloat(testfloat_gen, cmdline_opts):
    # Generate 100,000 test cases from testfloat.
    testfloat_data = testfloat_gen("f32_add", level=2, n=100000, extra_args="-tininessafter -rnear_even")

    # Truncate the error flags here because we don't want them.
    # testfloat_data = [test_case[0:3] for test_case in testfloat_data]
    for test_case in testfloat_data:
        test_case.append(Bits1(1)) # control bit 1=tininessafter
        test_case.append(Bits1(0)) # subOp bit 
        test_case.append(Bits3(0)) # rounding mode 0=rnear even

    run_test_vector_sim(
        addRecFN(8, 23),  # dut
        [("a b out* exceptionFlags* control roundingMode subOp"), *testfloat_data],  # test cases
        cmdline_opts,
    )

    # print(testfloat_data)
