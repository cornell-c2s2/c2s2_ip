import random

import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock

# Global Params ------------------------------------------------------------
NUM_HASHES = 8
LFSR_SEEDS = [
    0x0A89687E,
    0xA87DED5F,
    0x481C5077,
    0x81595729,
    0xFFD39769,
    0x24B05D57,
    0x9913B1FD,
    0xD8DF8ED2,
]
MISR_SIGNATURES = [
    0x2435B217,
    0xB25E4D4C,
    0x16307BD1,
    0x2CED25E0,
    0xC5145CCB,
    0x6180254B,
    0xC329C75C,
    0x89B9C2EC,
]

# Helper tasks -------------------------------------------------------------
async def start(dut):
    dut.reset.value = 1

    await ClockCycles(dut.clk, 2)
    assert dut.state.value == 0

    dut.reset.value = 0

    # start LBIST
    dut.lbist_req_val.value = 1
    dut.lfsr_resp_rdy.value = 1
    dut.misr_req_rdy.value = 1

    dut.lbist_resp_rdy.value = 0
    dut.misr_resp_val.value = 0

    await ClockCycles(dut.clk, 2)

    dut.lbist_req_val.value = 0
    dut.lfsr_resp_rdy.value = 0
    dut.misr_req_rdy.value = 0

async def sig_test_gen(dut, num_hashes, seeds, signatures, expected):
    seeds = seeds[::-1]
    signatures = signatures[::-1]
    expected = expected & (2**num_hashes - 1)

    await start(dut)

    for i in range(num_hashes):
        # check that message to LFSR is correct
        assert dut.state.value == 1
        assert dut.lfsr_resp_msg.value == seeds[i]

        # simulate calculation time
        await ClockCycles(dut.clk, 8)
        assert dut.state.value == 1
        
        # check that message to MISR is correct
        assert dut.misr_req_msg.value == dut.NUM_HASHES.value

        # simulate MISR hash response
        dut.misr_resp_val.value = 1
        dut.misr_resp_msg.value = signatures[i]

        await ClockCycles(dut.clk, 2)
        assert dut.state.value == 2

        dut.misr_resp_val.value = 0
        dut.misr_resp_msg.value = 0

        await ClockCycles(dut.clk, 2)

    # assert signature match bits
    assert dut.state.value == 2
    assert dut.lbist_resp_msg.value == expected

    dut.lbist_resp_rdy.value = 1
    await ClockCycles(dut.clk, 2)
    assert dut.state.value == 0

# Tests --------------------------------------------------------------------
# Tests to verify signature comparison logic
@cocotb.test()
async def signature_comparison_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    # test all possible perturbations of MISR_SIGNATURES
    for exp in range(2**NUM_HASHES):
        sig = MISR_SIGNATURES.copy()
        for bit in range(NUM_HASHES):
            if (exp & (2 ** (NUM_HASHES - bit - 1))) == 0:
                sig[bit] += 1
        await sig_test_gen(dut, NUM_HASHES, LFSR_SEEDS, sig, exp)

# Directed test for LFSR interface
@cocotb.test()
async def lfsr_interface_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

    await start(dut)
    
    assert dut.lfsr_resp_msg.value == LFSR_SEEDS[-1]
    assert dut.lfsr_resp_val.value == 1
    
    # simulate calculation time
    await ClockCycles(dut.clk, 8)

    assert dut.lfsr_resp_msg.value == LFSR_SEEDS[-1]
    assert dut.lfsr_resp_val.value == 1
    
    dut.misr_resp_val.value = 1
    await ClockCycles(dut.clk, 2)

    assert dut.lfsr_resp_msg.value == 0;
    assert dut.lfsr_resp_val.value == 0;

# Directed test for MISR interface
@cocotb.test()
async def misr_interface_test(dut):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    
    await start(dut)

    assert dut.misr_req_msg.value == NUM_HASHES
    assert dut.misr_req_val.value == 1
    assert dut.misr_resp_rdy.value == 0

    # simulate calculation time
    await ClockCycles(dut.clk, 8)

    dut.misr_resp_val.value = 1
    await ClockCycles(dut.clk, 2)

    assert dut.misr_req_msg.value == 0
    assert dut.misr_req_val.value == 0
    assert dut.misr_resp_rdy.value == 1
