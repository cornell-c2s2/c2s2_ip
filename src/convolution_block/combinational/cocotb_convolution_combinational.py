import cocotb
from cocotb.triggers import Timer
import random


async def conv_test_gen(dut, input_arr, filter):
    assert len(input_arr) == len(filter)

    dut.input_msg.value = input_arr
    dut.filter_msg.value = filter

    dut.clk.value = 0
    dut.reset.value = 0
    await Timer(1, units="ns")
    dut.clk.value = 1
    await Timer(1, units="ns")

    # assert that convolution has multiplied values correctly
    out = dut.output_msg.value
    for i in range(len(out)):
        assert out[i].integer == input_arr[i] * filter[len(out) - i - 1]


@cocotb.test()
async def multiply_tests(dut):
    # set parameters to module defaults
    BIT_WIDTH = 32
    ARRAY_LENGTH = 8

    # positive integer testing
    for _ in range(1000):
        input_arr = random.choices(
            population=range(2 ** (BIT_WIDTH // 2)), k=ARRAY_LENGTH
        )
        filter = random.choices(population=range(2 ** (BIT_WIDTH // 2)), k=ARRAY_LENGTH)
        await conv_test_gen(dut, input_arr, filter)
