import random
from dataclasses import dataclass
from typing import Optional
from collections import deque

import cocotb
import cocotb.simulator
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory
# from pymtl import mk_bits, concat

if cocotb.simulator.is_running():
    NBITS = int(cocotb.top.nbits.value)
    NOUTPUTS = int(cocotb.top.noutputs.value)
    N_ADDR_BITS = int(cocotb.top.n_addr_bits.value)


# Creates a random number spec given a range of nbits and noutputs
# Function pulled from pymtl testbench
# def router_spec(nbits, noutputs):
#     if isinstance(nbits, int):
#         nbits = (nbits, nbits)
#     if isinstance(noutputs, int):
#         noutputs = (noutputs, noutputs)

#     # Generate a random number of bits between bounds
#     nbits = random.randint(nbits[0], nbits[1])
#     # Random number of outputs, guarantees that it fits within nbits
#     noutputs = random.randint(noutputs[0], min(noutputs[1], (1 << nbits) - 1))

#     return nbits, noutputs

# Creates an input message to the router as well as returning the expected output index
# Function pulled from pymtl testbench
def gen_msg():
    # Number of bits needed to represent the output index
    n_addr_bits = (NOUTPUTS - 1).bit_length()
    n_data_bits = NBITS - n_addr_bits

    # random address and data
    addr = random.randint(0, NOUTPUTS - 1)
    data = random.randint(0, (1 << n_data_bits) - 1)

    return ((addr << (n_data_bits)) + data, addr)

# async def router_test(dut, p):
#     cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
#     random.seed(0x01234567)
#     nbits, noutputs = router_spec(p.nbits, p.noutputs) 
#     model = None  
#     assert model is not None, "TODO"

#     msgs = []
#     expected_outptus = [[] for _ in range(noutputs)]
#     for _ in range(p.nmsgs):
#         msg, adder = router_msg(nbits, noutputs)
#         msgs.append(msg)
#         expected_outptus[addr].append(msg)
    

# @cocotb.test()
# async def default_test(dut):
#     if not (p.nbits, p.noutputs == 32, 16):
#         return

#     nbits, noutputs = 32, 8

#     msgs = []
#     expected_outputs = [[] for _ in range(noutputs)]
#     for _ in range(p.nmsgs):
#         msg, addr = router_msg(nbits, noutputs)
#         msgs.append(msg)
#         expected_outputs[addr].append(msg)

        

# p_values = [
#     RTP(0, 8, 16, 20, 0, 0, None),
#     RTP(0, 8, 16, 20, 2, 2, None),
#     RTPL(
#         execution_num=list(range(10)),   # Do 10 tests
#         nbits=[(8, 32)],                 # Test 8-32 bit routers
#         noutputs=[(2, 16)],              # Test 2-16 output routers
#         nmsgs=[5],                       # Send 50 messages
#         src_delay=[0, 1, 8],             # Wait this many cycles between inputs
#         sink_delay=[0, 1, 8],            # Wait this many cycles between outputs
#         slow=True),
# ]
# factory = TestFactory(router_test)
# factory.add_option("p", p_values)
# factory.generate_tests()

async def run_simulation(dut, src_messages: deque, expected_sink):
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    dut.reset.value = 1
    dut.ostream_rdy.value = [1] * NOUTPUTS
    dut.istream_val.value = 0

    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0

    sink_messages = [deque() for _ in range(NOUTPUTS)]
    for _ in range(10000):
        await ClockCycles(dut.clk, 1)
        
        if dut.istream_rdy.value:
            if src_messages:
                dut.istream_msg = src_messages.popleft()
                dut.istream_val.value = 1
            else:
                dut.istream_val.value = 0
        
        for i, val in enumerate(dut.ostream_val.value):
            if val == 1:
                sink_messages[i].append(dut.ostream_msg.value[i])

    
    for i in range(NOUTPUTS):

        assert tuple(sink_messages[i]) == tuple(expected_sink[i])




@cocotb.test()
async def priority_test(dut):
    """Tests that the router routes the message to the correct output."""

    assert N_ADDR_BITS >= 3 and NOUTPUTS >= 8
    
    msgs = deque()
    expected = [deque() for _ in range(NOUTPUTS)]
    dests = [0, 1, 2, 3, 4, 5, 6, 7]
    for i in dests:
        msg = (dests[i] << (NBITS - N_ADDR_BITS)) + (dests[i] + 1)
        msgs.append(msg)
        expected[i].append(msg)
    
    await run_simulation(dut, msgs, expected)
    

@cocotb.test
async def random_test(dut):
    random.seed(0x01234567)

    msgs = deque()
    expected_outputs = [deque() for _ in range(NOUTPUTS)]
    nmsgs = 100
    for _ in range(nmsgs):
        msg, addr = gen_msg()
        msgs.append(msg)
        expected_outputs[addr].append(msg)

    await run_simulation(dut, msgs, expected_outputs)




    
    




# @cocotb.test()
# async def basic_test(dut):
#     cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
#     assert True

    # dut.reset.value = 1
    # await ClockCycles(dut.clk, 1)
    # dut.reset.value = 0

    # dut.recv_msg.value = 1
    # await ClockCycles(dut.clk, 1)
    # dut._log.info("Hello world!")
    # assert dut.send_msg.value == dut.recv_msg.value

# @cocotb.test()
# async def randomized_test(dut):
#     cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
#     dut.reset.value = 1
#     p = RTP(20, 32, 8, 20)
#     await ClockCycles(dut.clk, 1)
#     dut.reset.value = 0

#     for i in range(100):
#         msg = router_spec(p.nbits, p.noutputs)
#         dut.istream_msg.value = msg
#         dut.istream_val.value = 1
#         # dut.recv_msg.value = random.randint(0, 2 ** 20 - 1)
#         good = False
#         for i in range(len(p.noutputs)):
#             if dut.ostream_val.value[i] and dut.ostream_msg[i] == dut.istream_msg:
#                 good = True
#                 break
#         assert good
        
#         await ClockCycles(dut.clk, 1)
#         dut.istream_val.value = 0
#         dut.reset.value = 1
#         await ClockCycles(dut.clk, 1)
#         dut.reset.value = 0
#         await ClockCycles(dut.clk, 1)
    

    
