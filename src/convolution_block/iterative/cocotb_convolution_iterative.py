import cocotb
from cocotb.triggers import Timer
import random


async def conv_test_gen(dut, input_arr, filter, bit_width):
    assert len(input_arr) == len(filter)

    # cocotb seems to set/read arrays in reverse order
    # so, input and output arrays have to be reversed when interfacing with the dut
    dut.input_msg.value = input_arr[::-1]
    dut.filter_msg.value = filter[::-1]

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

    # cycle for BIT_WIDTH + 2 cycles so that the iterative multipliers can complete their task
    # this requirement comes from the fixed point iterative multiplier
    for cycle in range(bit_width + 2):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

    # output array is reversed for the same reason the input arrays are
    out = dut.output_msg.value[::-1]

    # assert that convolution has multiplied values correctly
    for i in range(len(out)):
        assert dut.output_val
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
        await conv_test_gen(dut, input_arr, filter, BIT_WIDTH)
