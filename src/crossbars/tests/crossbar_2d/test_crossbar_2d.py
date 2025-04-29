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