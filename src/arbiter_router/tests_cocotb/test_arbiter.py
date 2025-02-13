import random
import math
from dataclasses import dataclass

import cocotb
import cocotb.simulator
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory

if cocotb.simulator.is_running():
    NBITS = int(cocotb.top.nbits.value)
    NINPUTS = int(cocotb.top.ninputs.value)
    ADDR_NBITS = int(cocotb.top.addr_nbits.value)
    assert ADDR_NBITS == math.ceil(math.log2(NINPUTS))
    # assert False, "boo hoo"


def sim_arbiter(nbits, ninputs, nmsgs, delay):
    # Create a bunch of messages
    raise NotImplemented()


def is_default():
    """[is_default()] returns [True] if the current Verilog parameters match 
    the default scenario."""
    return NBITS == 32, NINPUTS == 3, ADDR_NBITS == 2

    
def construct_out(msg, addr):
    return (addr << NBITS) + msg



def functional_arbitrate(valids):
    """Functional model for arbitrating"""
    for i, val in enumerate(valids):
        if val:
            return i


@cocotb.test()
async def priority_test(dut):
    """Tests that the arbiter prioritizes correctly if several inputs are 
    avaiable."""
    msgs = [0, 1, 2]

    async def one_run(valids, expected):
        dut.reset.value = 1
        await ClockCycles(dut.clk, 3)
        dut.reset.value = 0

        dut.istream_msg.value = msgs
        dut.istream_val.value = valids

        expected_out = construct_out(msgs[expected], expected)
        dut._log.info("expected", expected_out)
        await ClockCycles(dut.clk, 1)

        assert dut.ostream_msg.value == expected_out, f"expected {expected_out}, got {dut.ostream_msg.value}"

    if not is_default():
        return
    
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    dut.ostream_rdy.value = 1

    await one_run([0, 0, 1], 2)
    await one_run([1, 0, 0], 0)
    await one_run([0, 1, 0], 1)
    await one_run([1, 0, 1], 0)
    await one_run([1, 1, 1], 0)
    await one_run([0, 1, 1], 1)
    await one_run([1, 1, 0], 0)


async def priority_test_w_delays(dut, delay, nmsgs=20):
    """Tests that the arbiter prioritizes correctly if several inputs are 
    avaiable. Tests a variety of delays. Adapted from PyMTL tests."""
    if not is_default():
        return
    
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    # msgs = [
    #     [random.randint(0, (1 << NBITS) - 1) for _ in range(nmsgs)]
    #     for _ in range(NINPUTS)
    # ]
    msgs = [
        [0 for _ in range(nmsgs)]
        for _ in range(NINPUTS)
    ]

    dut.reset.value = 1
    await ClockCycles(dut.clk, 3)
    dut.reset.value = 0
    dut.ostream_rdy.value = 1
    
    msg_indices = [0 for _ in range(NINPUTS)]
    istream_val = [0 for _ in range(NINPUTS)]
    dut.istream_val.value = istream_val

    istream_msg = [msgs[i][0] for i in range(NINPUTS)]
    dut.istream_msg.value = istream_msg

    expected_output = []
    cycle = 0
    prev_pick = None
    
    for _ in range(10000):
        dut._log.info(f"starting cycle {cycle}")
        dut._log.info(f"starting msg_indices = {msg_indices}")

        if cycle % (delay + 1) == 0:
            # Send inputs every 'delay + 1' cycles.
            dut._log.info(f"sending inputs, cycle is {cycle}")
            for i in range(NINPUTS):
                if msg_indices[i] < nmsgs:
                    dut._log.info(f"updating valid, valids={istream_val}")
                    istream_val[i] = 1

        dut.istream_val.value = istream_val
        # dut.istream_msg.value = [msgs[i][msg_indices[i]] for i in range(NINPUTS)]
        dut.istream_msg.value = istream_msg
        await ClockCycles(dut.clk, 1)
        dut._log.info(f"istream_val = {dut.istream_val.value}")

        
        for i in range(NINPUTS):
            if prev_pick is not None and istream_val[prev_pick] and i != prev_pick:
                continue

            if istream_val[i]:

                # expected_output.append(construct_out(msgs[i], i))
                expected = construct_out(msgs[i][msg_indices[i]], i)
                assert dut.ostream_msg.value == expected, f"expected input {expected >> 32} to be picked, but input {dut.ostream_msg.value >> 32} was picked instead"
                dut._log.info(f"arbiter picked input {i}")
                prev_pick = i
                msg_indices[i] += 1
                
                if msg_indices[i] < nmsgs:
                    istream_msg[i] = msgs[i][msg_indices[i]]

                istream_val[i] = 0
                break
        else:
            prev_pick = None
            
        if all(i >= nmsgs for i in msg_indices):
            break
        
        dut._log.info(f"end of cycle {cycle}\n")
        cycle += 1
        # await ClockCycles(dut.clk, 1)
    else:
        assert False, "cycle limit exceed (this is for defensive reasons, simulation not necessarily incorrect)"


delay_values = [0, 1, 2, 3, 4, 8]
factory = TestFactory(priority_test_w_delays)
factory.add_option("delay", delay_values)
factory.generate_tests()





# @cocotb.test()
# async def test_arbiter(dut):
#     cocotb.start_soon(Clock(dut.clk, 1, "ns").start())

#     assert False, "hello world"

#     dut.reset.value = 1
#     await ClockCycles(dut.clk, 1)
#     dut.reset.value = 0

#     dut.recv_msg.value = 1
#     await ClockCycles(dut.clk, 1)
#     dut._log.info("Hello world!")
#     assert dut.send_msg.value == dut.recv_msg.value

# @cocotb.test()
# async def randomized_test(dut):
#     cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
#     assert False, "hello world"
#     dut.reset.value = 1
#     await ClockCycles(dut.clk, 1)
#     dut.reset.value = 0

#     for i in range(100):
#         dut.recv_msg.value = random.randint(0, 2 ** 20 - 1)
#         assert dut.send_msg.value == dut.recv_msg.value
#         await ClockCycles(dut.clk, 1)
    

    
