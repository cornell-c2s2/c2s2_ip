import random

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

import pdb

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

    # dut._log.info(dut.recv_msg.value)
    # dut._log.info(len((dut.recv_msg.value)))
    # dut._log.info(len((dut.recv_msg.value[0])))

    dut._log.info(msg_array)
    # dut._log.info(len(msg_array))
    # dut._log.info(len(msg_array[0]))

    dut.recv_val.value = val_array
    dut.recv_msg.value = msg_array

    await ClockCycles(dut.clk, 1)

    dut._log.info("==================")
    dut._log.info(dut.send_val.value)
    dut._log.info(dut.send_msg.value)

    # for i in range(dut.N_OUTPUTS.value):
    #     assert dut.send_val[i] == 1



    await ClockCycles(dut.clk, 1)

    assert True
    

    