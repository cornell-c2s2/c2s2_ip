import random
import math

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

import pdb
import crossbar_2d_func_model

@cocotb.test()
async def basic_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    dut._log.info(f"DUT parameters (BIT_WIDTH): {dut.BIT_WIDTH.value}")
    dut._log.info(f"DUT parameters (N_INPUTS): {dut.N_INPUTS.value}")
    dut._log.info(f"DUT parameters (N_OUTPUTS): {dut.N_OUTPUTS.value}")
    dut._log.info(f"DUT parameters (ENTRIES): {dut.ENTRIES.value}")

    await ClockCycles(dut.clk, 1)

    # Reset to 1
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    
    # Reset to 0
    dut.reset.value = 0

    dut.recv_val.value = [0]*dut.N_INPUTS.value
    dut.send_rdy.value = [0]*dut.N_OUTPUTS.value
    await ClockCycles(dut.clk, 1)

    val_array = []
    msg_array = []
    for i in range(dut.N_INPUTS.value):
        val_array.append(1)
        msg_array.append([dut.N_INPUTS.value - i]*dut.ENTRIES.value)

    dut._log.info(msg_array)

    dut.recv_val.value = val_array
    dut.recv_msg.value = msg_array

    await ClockCycles(dut.clk, 1)

    dut._log.info("==================")
    dut._log.info(dut.send_val.value)
    dut._log.info(dut.send_msg.value)


    for i in range(dut.N_OUTPUTS.value):
        assert dut.send_val[i] == (1 if i == 0 else 0), f"Mismatch in send_val at output {i}"

@cocotb.test()
async def randomized_control_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 2)

    for _ in range(10):
        random_control = random.randint(0, 2**dut.CONTROL_BIT_WIDTH.value - 1)
        dut.control.value = random_control
        dut.control_val.value = 1

        recv_msg = [[i for i in range(dut.ENTRIES.value)] for _ in range(dut.N_INPUTS.value)]
        dut.recv_msg.value = recv_msg
        dut.recv_val.value = [1]*dut.N_INPUTS.value
        dut.send_rdy.value = [1]*dut.N_OUTPUTS.value

        await ClockCycles(dut.clk, 2)

        send_msg, send_val, recv_rdy = crossbar_2d_func_model.crossbar_2d_func_model(
            recv_msg=recv_msg,
            recv_val=[1]*dut.N_INPUTS.value,
            send_rdy=[1]*dut.N_OUTPUTS.value,
            control=random_control,
            n_inputs=dut.N_INPUTS.value,
            n_outputs=dut.N_OUTPUTS.value,
            entries=dut.ENTRIES.value
        )

        for i in range(dut.N_OUTPUTS.value):
            dut_msg_ints = [dut.send_msg[i][j].value.integer for j in range(dut.ENTRIES.value)]
            assert dut_msg_ints == send_msg[i], f"Mismatch in send_msg at output {i}"

        for i in range(dut.N_OUTPUTS.value):
            assert dut.send_val[i].value.integer == send_val[i], f"Mismatch in send_val at output {i}"

        for i in range(dut.N_INPUTS.value):
            assert dut.recv_rdy[i].value.integer == recv_rdy[i], f"Mismatch in recv_rdy at input {i}"

    await ClockCycles(dut.clk, 1)
    assert True
#some directed tests on 2x2 (square crossbar),
#  4x2 (inputs>outputs),
#  2x4 (output>inputs) with all other parameters set to some constant (maybe the defaults). 
# This directed tests ensure that the inputs/outputs align. 
# Then, run random tests for different param values for the other parameters. 
# Run enough random tests to achieve 100% on all applicable signals.

@cocotb.test()
async def square_crossbar_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0

    # Setup
    recv_msg = [[11, 12], [21, 22]]
    recv_val = [1, 1]
    send_rdy = [1, 1]
    control = (1 << 1) | 0  # input_sel = 1, output_sel = 0

    dut.control.value = control
    dut.control_val.value = 1
    dut.recv_msg.value = recv_msg
    dut.recv_val.value = recv_val
    dut.send_rdy.value = send_rdy

    await ClockCycles(dut.clk, 2)

    assert [dut.send_msg[0][j].value.integer for j in range(2)] == [21, 22]
    assert dut.send_val[0].value.integer == 1
    assert dut.recv_rdy[1].value.integer == 1


@cocotb.test()
async def input_greater_than_output(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 2)
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0

    recv_msg = [[i*10 + j for j in range(2)] for i in range(dut.N_INPUTS.value)]
    recv_val = [1] * dut.N_INPUTS.value
    send_rdy = [1] * dut.N_OUTPUTS.value

    input_sel = dut.N_INPUTS.value - 1
    output_sel = min(1, dut.N_OUTPUTS.value - 1)

    input_sel_bits = math.ceil(math.log2(dut.N_INPUTS.value))
    output_sel_bits = math.ceil(math.log2(dut.N_OUTPUTS.value))
    control = ((input_sel << output_sel_bits) | output_sel)

    dut.control.value = control
    dut.control_val.value = 1
    dut.recv_msg.value = recv_msg
    dut.recv_val.value = recv_val
    dut.send_rdy.value = send_rdy

    await ClockCycles(dut.clk, 2)

    assert [dut.send_msg[output_sel][j].value.integer for j in range(2)] == recv_msg[input_sel]
    assert dut.send_val[output_sel].value.integer == 1
    assert dut.recv_rdy[input_sel].value.integer == 1

@cocotb.test()
async def output_greater_than_input(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0

    recv_msg = [[100 + j for j in range(2)] for _ in range(dut.N_INPUTS.value)]
    recv_val = [1] * dut.N_INPUTS.value
    send_rdy = [1] * dut.N_OUTPUTS.value

    input_sel = min(1, dut.N_INPUTS.value - 1)
    output_sel = dut.N_OUTPUTS.value - 1

    input_sel_bits = math.ceil(math.log2(dut.N_INPUTS.value))
    output_sel_bits = math.ceil(math.log2(dut.N_OUTPUTS.value))
    control = ((input_sel << output_sel_bits) | output_sel)

    dut.control.value = control
    dut.control_val.value = 1
    dut.recv_msg.value = recv_msg
    dut.recv_val.value = recv_val
    dut.send_rdy.value = send_rdy

    await ClockCycles(dut.clk, 2)

    assert [dut.send_msg[output_sel][j].value.integer for j in range(2)] == recv_msg[input_sel]
    assert dut.send_val[output_sel].value.integer == 1
    assert dut.recv_rdy[input_sel].value.integer == 1
