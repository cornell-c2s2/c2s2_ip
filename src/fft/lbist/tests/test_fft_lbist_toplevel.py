import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

# Helper tasks -------------------------------------------------------------
async def lbist_top_simple(dut):
    # Reset
    dut.reset.value = 1

    #Start clock
    await ClockCycles(dut.clk, 2)

    # Reset to 0
    dut.reset.value = 0
    await ClockCycles(dut.clk, 2)

    # Start LBIST
    dut.lbist_req_val.value = 1
    await ClockCycles(dut.clk, 2)

    # Wait until LBIST is finished
    counter = 0
    while dut.lbist_resp_val.value != 1:
        # if dut.lfsr_paramver2.state.value == 1:
        #     print(f"LFSR OUTPUT {counter}: {dut.lfsr_paramver2.resp_msg.value}")
        #     counter += 1
        # if dut.fft_pease_FFT.state == 2:
        #     print(f"FFT OUTPUT: {dut.fft_pease_FFT.send_msg.value}")
        # if dut.lbist_controller.misr_resp_val.value == 1:
        #     print(f"MISR output hash sent to controller")
        # if dut.lbist_controller.state.value == 2:
        #     counter = 0
        #     print(f"OUTPUT HASH: {dut.lbist_controller.misr_resp_msg.value}\n")
        await ClockCycles(dut.clk, 2)

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
