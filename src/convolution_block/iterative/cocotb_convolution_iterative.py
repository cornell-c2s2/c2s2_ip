import cocotb
from cocotb.triggers import Timer
import random


async def conv_test_gen(dut, input_arr, filter, BIT_WIDTH):
    assert len(input_arr) == len(filter)
    dut.input_msg.value = input_arr
    dut.filter_msg.value = filter

    dut.input_val.value = 1
    dut.filter_val.value = 1
    dut.output_rdy.value = 0

    # send a reset signal for one cycle to initialize the iterative multiplier counter
    dut.reset.value = 1
    dut.clk.value = 0
    await Timer(1, units="ns")
    dut.clk.value = 1
    await Timer(1, units="ns")
    dut.reset.value = 0

    # cycle for BIT_WIDTH + 2 clock cycles so that the multipliers can complete their operations
    # this length comes from the fixed point iterative multiplier
    for cycle in range(BIT_WIDTH + 2):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

    # assert that convolution has multiplied values correctly
    assert dut.output_val
    for i in range(len(input_arr)):
        assert dut.output_msg.value[i] == input_arr[i] * filter[len(input_arr) - i - 1]


@cocotb.test()
async def multiply_tests(dut):
    # set parameters to module defaults
    BIT_WIDTH = 32
    ARRAY_LENGTH = 8

    # randomized testing
    for _ in range(1000):
        input_arr = random.choices(
            population=range(2 ** (BIT_WIDTH // 2)), k=ARRAY_LENGTH
        )
        filter = random.choices(population=range(2 ** (BIT_WIDTH // 2)), k=ARRAY_LENGTH)
        await conv_test_gen(dut, input_arr, filter, BIT_WIDTH)
