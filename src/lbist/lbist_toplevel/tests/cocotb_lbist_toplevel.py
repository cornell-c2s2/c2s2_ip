import cocotb
from cocotb.triggers import Timer
import random


async def lbist_test_gen(dut):
    # send a reset signal for one cycle
    dut.reset.value = 1
    dut.clk.value = 0
    await Timer(1, units="ns")
    dut.clk.value = 1
    await Timer(1, units="ns")
    dut.reset.value = 0
    
    dut.lbist_req_val.value = 1
    
    while dut.lbist_resp_val.value != 1:
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")
        
        # if dut.lfsr.state.value == 2:
        dut._log.info(f"lfsr output: {dut.lfsr_cut_resp_msg}")

        # if dut.lbist_controller.state == 2:
        #     dut._log.info(f"hash: {dut.lbist_controller.misr_resp_msg}")

        # dut._log.info(f"controller state: {dut.lbist_controller.state}")
        # dut._log.info(f"a: {dut.cut.a}")
        # dut._log.info(f"b: {dut.cut.b}")
        # dut._log.info(f"c: {dut.cut.c}")
        # if dut.ctrl_misr_req_val.value == 1:
        #     dut._log.info(f"controller state: {dut.lbist_controller.state}")
        #     dut._log.info(f"max output hash parameter: {dut.lbist_controller.MAX_OUTPUTS_TO_HASH}")
        #     dut._log.info(f"misr req msg bits: {dut.lbist_controller.MISR_MSG_BITS}")
        #     dut._log.info(f"misr req msg: {dut.lbist_controller.misr_req_msg}")
        #     dut._log.info(f"misr resp rdy: {dut.lbist_controller.misr_resp_rdy}")
        #     dut._log.info("")

        # if dut.cut_misr_resp_val.value == 1:
        #     dut._log.info(f"misr state: {dut.misr.state}")
        #     dut._log.info(f"misr hashed count: {dut.misr.outputs_hashed}")
        #     dut._log.info(f"misr hashed target: {dut.misr.outputs_to_hash}")
        #     dut._log.info(f"misr lbist req msg: {dut.misr.lbist_req_msg}")
        #     dut._log.info(f"lbist misr req msg: {dut.lbist_controller.misr_req_msg}")
        #     dut._log.info(f"ctrl misr req msg: {dut.ctrl_misr_req_msg}")
        #     dut._log.info(f"MISR: max outputs to hash: {dut.misr.MAX_OUTPUTS_TO_HASH}")
        #     dut._log.info(f"MISR: msg bits: {dut.misr.LBIST_MSG_BITS}")
        #     dut._log.info(f"CTRL: max outputs to hash: {dut.lbist_controller.MAX_OUTPUTS_TO_HASH}")
        #     dut._log.info(f"CTRL: msg bits: {dut.lbist_controller.MISR_MSG_BITS}")
        #     dut._log.info("")
            
    dut._log.info(f"TEST OUTPUT: {dut.lbist_resp_msg.value}")
    assert dut.lbist_resp_msg.value == 0b11111111


@cocotb.test()
async def toplevel_tests(dut):
    await lbist_test_gen(dut)
