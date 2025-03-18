import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

# Helper tasks -------------------------------------------------------------
async def lbist_top_simple(dut):
    dut.reset.value = 1
    await ClockCycles(dut.clk, 2)

    dut.reset.value = 0
    await ClockCycles(dut.clk, 2)

    # Start LBIST
    dut.lbist_req_val.value = 1
    await ClockCycles(dut.clk, 2)

    # for some reason this was necessary to get the debugging to work ?
    # print(f"{dir(dut.fft_pease_FFT.fft_stage)}")
    # print(f"{dir(dut.fft_pease_FFT.fft_stage.mult)}")

    # Wait until LBIST is finished
    counter = 0
    while dut.lbist_resp_val.value != 1:
        
        # debugging for rounding error
        # for i in range(4):
        #     dut._log.info(f"AR: {hex(dut.fft_pease_FFT.fft_stage.ar.value[i])}, AC: {hex(dut.fft_pease_FFT.fft_stage.ac.value[i])}")
        #     dut._log.info(f"BR: {hex(dut.fft_pease_FFT.fft_stage.br.value[i])}, BC: {hex(dut.fft_pease_FFT.fft_stage.bc.value[i])}")
        #     dut._log.info(f"WR: {hex(dut.fft_pease_FFT.fft_stage.wr.value[i])}, WC: {hex(dut.fft_pease_FFT.fft_stage.wc.value[i])}")
        #     dut._log.info(f"M_CR: {hex(dut.fft_pease_FFT.fft_stage.m_cr.value[i])}, M_CC: {hex(dut.fft_pease_FFT.fft_stage.m_cc.value[i])}")
        #     dut._log.info(f"CR: {hex(dut.fft_pease_FFT.fft_stage.cr.value[i])}, CC: {hex(dut.fft_pease_FFT.fft_stage.cc.value[i])}")
        #     dut._log.info(f"DR: {hex(dut.fft_pease_FFT.fft_stage.dr.value[i])}, DC: {hex(dut.fft_pease_FFT.fft_stage.dc.value[i])}")
        #     dut._log.info("")
        #     dut._log.info(f"C_AR: {hex(dut.fft_pease_FFT.fft_stage.mult.c_ar.value)}, C_AC: {hex(dut.fft_pease_FFT.fft_stage.mult.c_ac.value)}")
        #     dut._log.info(f"C_BR: {hex(dut.fft_pease_FFT.fft_stage.mult.c_br.value)}, C_BC: {hex(dut.fft_pease_FFT.fft_stage.mult.c_bc.value)}")
        #     dut._log.info(f"C_CR: {hex(dut.fft_pease_FFT.fft_stage.mult.cr.value)}, C_CC: {hex(dut.fft_pease_FFT.fft_stage.mult.cc.value)}")
        #     dut._log.info("")
        #     dut._log.info(f"arXbr: {hex(dut.fft_pease_FFT.fft_stage.mult.arXbrMult.c.value)}")
        #     dut._log.info(f"acXbc: {hex(dut.fft_pease_FFT.fft_stage.mult.acXbcMult.c.value)}")
        #     dut._log.info(f"arXbrc: {hex(dut.fft_pease_FFT.fft_stage.mult.arXbrcMult.c.value)}")
        #     dut._log.info(f"cr: {hex(dut.fft_pease_FFT.fft_stage.mult.cr.value)}")
        #     dut._log.info(f"cc: {hex(dut.fft_pease_FFT.fft_stage.mult.cc.value)}")
        #     dut._log.info("\n\n")
        
        # if dut.fft_pease_FFT.recv_val.value == 1 and dut.fft_pease_FFT.recv_rdy.value == 1:
        #     for v in dut.fft_pease_FFT.reversed_msg.value:
        #         dut._log.info(f"{hex(v)}")

        # if dut.lfsr_cut_reset.value == 1:
        #     dut._log.info("\n")

        await ClockCycles(dut.clk, 1)

    dut._log.info(f"TEST OUTPUT: {dut.lbist_resp_msg.value}")

    # Ensure all tests passed!
    result = str(dut.lbist_resp_msg.value)
    passed = 0
    failed = 0
    total = len(result)
    for i in range(dut.NUM_SEEDS.value):
        if result[i] == '1':
            passed += 1
        else:
            failed += 1
    
    assert passed == total, f"Passed tests: {passed}, Total tests: {total}"

# Tests --------------------------------------------------------------------
# Single directed test
@cocotb.test()
async def lbist_top_test1(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    await lbist_top_simple(dut)
