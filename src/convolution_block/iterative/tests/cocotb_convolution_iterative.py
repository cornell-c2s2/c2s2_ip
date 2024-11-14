import cocotb
from cocotb.triggers import Timer
import random


async def conv_test_gen(dut, input_arr, filter, BIT_WIDTH, random_max):
    assert len(input_arr) == len(filter)

    # random delay
    for _ in range(random.randint(0, random_max)):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

    dut.req1_msg.value = input_arr
    dut.req1_val.value = 1

    # random delay
    for _ in range(random.randint(0, random_max)):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

    dut.req2_msg.value = filter
    dut.req2_val.value = 1

    # random delay
    for _ in range(random.randint(0, random_max)):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

    dut.resp_rdy.value = 0

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

    dut.req1_val.value = 0
    dut.req2_val.value = 0
    dut.resp_rdy.value = 1

    # assert that convolution has multiplied values correctly
    assert dut.resp_val
    out = dut.resp_msg.value
    for i in range(len(out)):
        expected = (input_arr[i] * filter[len(out) - i - 1]) & ((1 << BIT_WIDTH) - 1)
        assert out[i] == expected


@cocotb.test()
async def multiply_tests(dut):
    # set parameters to module defaults
    BIT_WIDTH = 32
    ARRAY_LENGTH = 8

    random_delay = 10

    # randomized testing
    for _ in range(1000):
        input_arr = random.choices(population=range(2 ** (BIT_WIDTH)), k=ARRAY_LENGTH)
        filter = random.choices(population=range(2 ** (BIT_WIDTH)), k=ARRAY_LENGTH)
        await conv_test_gen(dut, input_arr, filter, BIT_WIDTH, random_delay)
