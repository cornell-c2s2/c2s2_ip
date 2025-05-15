# ===================================================================
# Author: Johnny Martinez, Tean Lai, Akshati Vaishnav
# Date: 05/14/2025
# 
# Spec: This is the cocotb testbench for the Spring 25 top-level.
# 
#   < FILL >
#  
# *** Only run tests with test factories and not @cocotb.test()
# ===================================================================
import random
from enum import Enum
import cocotb
from cocotb.triggers import Timer, Edge, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.regression import TestFactory
from pymtl3 import *
from fixedpt import Fixed, CFixed
from src.tapeins.sp25.tapein1.tests.spi_driver_sim import spi_write_read, spi_write, spi_read
from src.classifier.sim import classify, frequency_bins
from src.classifier.tests_cocotb.classifier_model import classify
from src.fft.tests.fft import FFTInterface, FFTPease
from tools.utils import fixed_bits
from cfg_interconnects import *
import spi_interface as phy



# Parameters ------------------------------------------------------------------
# - SEED: Seed value to ensure deterministic random values.
# - USB_PORT: Path to SPI Driver (only needed for FPGA Emulation).
#             "/dev/ttyUSB0" is the typical value, but can be different.
# - DEBUG_ENABLED: True if you want to enable printouts. False otherwise
#                  When you want to print, write: 
#                  " DEBUG_ENABLED and dut._log.info("<INFO>") "
# - FPGA_EMULATION: True if you are driving FPGA. False if you are purely 
#                   simulating the DUT.
# - RUN_SPI_TESTS: True if you want to run tests driving DUT with SPI Driver.
# - RUN_ASYNC_FIFO_TESTS: True if you want to run tests driving DUT with Async
#                         FIFO.
# - RUN_LOOPBACK_TESTS: True if you want to run loopback tests.
# - RUN_FFT_TESTS: True if you want to run FFT tests.
# - RUN_CLASSIFIER_TESTS: True if you want to run tests for the classifier module.
# - RUN_FFT_CLASSIFIER_TESTS: True if you want to run tests where FFT output is
#                             passed to the classifier.
# - RUN_LBIST_TESTS: True if you want to run Logic Built-In Self-Test (LBIST) 
#                    tests.

SEED = "C2S2"
USB_PORT =  "/dev/ttyUSB0"
DEBUG_ENABLED = False
FPGA_EMULATION = True
RUN_SPI_TESTS = True
RUN_ASYNC_FIFO_TESTS = True
RUN_LOOPBACK_TESTS = True
RUN_FFT_TESTS = True
RUN_CLASSIFIER_TESTS = True
RUN_FFT_CLASSIFIER_TESTS = True
RUN_LBIST_TESTS = True

# Housekeeping ----------------------------------------------------------------
# Set seed to ensure determinisitic random values.
random.seed(SEED)

# Extract parameter values from DUT
if cocotb.simulator.is_running():
    ADDR_BITS = int(cocotb.top.ADDR_BITS.value)
    DATA_BITS = int(cocotb.top.DATA_BITS.value)
    SPI_PACKET_BITS = int(cocotb.top.SPI_PACKET_BITS.value)


# Desc: Basic Test to ensure design compiles
@cocotb.test()
async def basic_test(dut):
    """This test just checks if things compile!"""
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await ClockCycles(dut.clk, 10)

    DEBUG_ENABLED and dut._log.info("Design compiles!")
    assert True

# Helper Functions ------------------------------------------------------------
# Desc: Run src/sink testing.SRC/SNK msgs are converted to SPI protocol 
# transactions. Testing is done at the transaction level.
#
# Args:
#   - dut: model for top
#   - in_msgs: a list of input messages
#   - out_msgs: a list of expected output messages
#   - max_trsns: The maximum number of transactiosn to run. The test
#                fails if the simulation takes too long.
async def run_top_SPI(
    dut,
    in_msgs: list[int],
    out_msgs: list[int],
    max_trsns=30,
    curr_trsns=0
):
    if FPGA_EMULATION:
        phy.init_usb(USB_PORT)
        phy.spi_trigger_a(0.05)
    
    # SPI messages
    DEBUG_ENABLED and dut._log.info(f"in_msgs = {in_msgs}")
    DEBUG_ENABLED and dut._log.info(f"out_msgs = {out_msgs}")
    mk = mk_bits(SPI_PACKET_BITS)

    in_msgs = [mk(x) for x in in_msgs]
    out_msgs = [mk(x) for x in out_msgs]

    in_idx = 0
    out_idx = 0
    trsns = curr_trsns + 1
    spc = 0

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"

        # The following logging statements are for debugging purposes. Feel free
        # to modify them as needed.
        DEBUG_ENABLED and dut._log.info("\nnew loop!")
        DEBUG_ENABLED and dut._log.info(f"spc = {spc}")

        # Use SPI to send and receive data
        if in_idx < len(in_msgs) and spc == 1:
            if FPGA_EMULATION:
                spi_status, _, retmsg = phy.spi_write_read(in_msgs[in_idx])
            else:
                spi_status, retmsg = await spi_write_read(dut, in_msgs[in_idx])

            DEBUG_ENABLED and dut._log.info(
                f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}, sending in {hex(in_msgs[in_idx])}"
            )
            spc = spi_status[0]

            if spi_status[1] == 1:
                assert retmsg == out_msgs[out_idx]
                out_idx += 1
            in_idx += 1

        else:
            if FPGA_EMULATION:
                spi_status, send, retmsg= phy.spi_read()
            else:
                spi_status, retmsg = await spi_read(dut)
            DEBUG_ENABLED and dut._log.info(f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}")
            spc = spi_status[0]
            if spi_status[1] == 1:
                assert retmsg == out_msgs[out_idx]
                out_idx += 1

        trsns += 1

    return trsns - 1



# Desc: Drives inputs to Async FIFO
#
# Args:
#   - dut: model for top
#   - in_msgs: a list of input messages
#   - out_msgs: a list of expected output messages
#   - max_trsns: The maximum number of transactiosn to run. The test
#                fails if the simulation takes too long.
#   - num_config: <TODO: FILL>
async def run_top_AsyncFIFO(
    dut,
    in_msgs: list[int],
    out_msgs: list[int],
    max_trsns=30,
    curr_trsns=0,
    num_config=0
):
    """
    Run src/sink testing. src/snk msgs are converted to SPI protocol transactions.
    Testing is done at the transaction level.

    Args:
    dut: model for top
    in_msgs: a list of input messages
    out_msgs: a list of expected output messages
    max_trsns: the maximum number of transactions to run. test will fail if
      simulations take too long
    curr_trsns: the current transaction number (note from Tean: I've ported this
      over from previous testbenches for now, but I'm thinking of possibly removing it)
    peel: optional parameter to peek at the output messages (DO NOT REMOVE THIS - Johnny Martinez JJM469)
    """
    # SPI messages
    DEBUG_ENABLED and dut._log.info(f"in_msgs = {in_msgs}")
    DEBUG_ENABLED and dut._log.info(f"out_msgs = {out_msgs}")
    mk = mk_bits(SPI_PACKET_BITS)
    config_msgs = []
    in_msgs_fifo = []

    mk_fifo_config = mk_bits(8)
    config_msgs = [mk(x) for x in in_msgs[:num_config]]
    in_msgs_fifo = [mk_fifo_config(x) for x in in_msgs[num_config:]]

    in_idx = 0
    out_idx = 0
    trsns = curr_trsns + 1

    spc = 0

    # FIFO messages
    fifo_in = [int(x) for x in in_msgs_fifo]
    fifo_out = [int(x) for x in out_msgs]

    # access FIFO submodule
    fifo = dut.async_fifo
    fifo_config_done = 0

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"
        
        # The following logging statements are for debugging purposes. Feel free
        # to modify them as needed.
        DEBUG_ENABLED and dut._log.info("\nnew loop!")
        DEBUG_ENABLED and dut._log.info(f"spc = {spc}")

        # Use ASYNC FIFO to sent input data, router to send configuration messages, arbiter to receive messages
        # Send in the SPI configuration messages for the path (only need to do this once!)
        if not fifo_config_done:
            # reset FIFO to 0
            fifo.async_rst.value = 0
            await ClockCycles(dut.clk, 1)

            for config_idx in range(len(config_msgs)):
                spi_status, retmsg = await spi_write(dut, config_msgs[config_idx])

            # reset FIFO to 1
            fifo.async_rst.value = 1
            await ClockCycles(dut.clk, 1)

            # reset FIFO to 0
            fifo.async_rst.value = 0

            # This needs to be 4 cycles to allow for values to change in the reg file
            await ClockCycles(dut.clk, 4)

            # only need to configure once
            fifo_config_done = 1

        # Send input FIFO msg if ready and haven't already sent current msg
        if fifo.istream_rdy.value == 1 and in_idx < len(fifo_in):
            fifo.istream_msg.value = fifo_in[in_idx] & 0xFF
            fifo.istream_val.value = 1
            await ClockCycles(dut.ext_clk, 2)
            in_idx += 1
            fifo.istream_val.value = 0
        else:
            await ClockCycles(dut.clk, 1)

        # wait for output from router
        spi_status, retmsg = await spi_read(dut)
        output_msg = mk(retmsg)

        spc = spi_status[0]

        # if SPI minion is valid
        if spi_status[1] == 1:
            assert (
                output_msg == out_msgs[out_idx]
            ), f"Output mismatch: got {hex(int(output_msg))}, expected {hex(int(out_msgs[out_idx]))}"
            # dut._log.info("[FIFO] Correct FIFO output message!")
            out_idx += 1

        trsns += 1

    return trsns - 1


# Desc: Resets the DUT
#
# Args:
#   - dut: model for top
async def reset_dut(dut):
    """
    Resets dut.
    """
    dut.reset.value = 1
    await ClockCycles(dut.clk, 1)
    dut.reset.value = 0
    await ClockCycles(dut.clk, 3)


# Desc: Make spi packet. Does bitwise operations to concatenate [addr] and [data]
# together to form a spi packet. The spi packet is equal to {addr, data}.
# Args:
#   - addr (int): Address field to be packed (must fit within ADDR_BITS bits)
#   - data (int): Data field to be packed (must fit within DATA_BITS bits)
# Returns:
#   int: A single integer representing the packed SPI packet
def mk_spi_pkt(addr: int, data: int) -> int:
    assert not data >> DATA_BITS
    assert not addr >> ADDR_BITS
    return (addr << DATA_BITS) | data
    

# =============================================================================
# SPI Tests 
# =============================================================================
# The following section defines the tests when driving the DUT with the SPI 
# driver. To omit a set of tests, set its corresponding parameter to false in 
# the parameters section at the top.
#
# Ex: To omit the loopback tests for the SPI driver, set RUN_SPI_TESTS = False
# and RUN_LOOPBACK_TESTS = False

# Loopback Tests --------------------------------------------------------------
async def test_loopback_noXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> arbiter -> spi.

    We expect the outputs' data to be the same as the inputs', their address
    bits might differ.
    """
    in_msgs = [mk_spi_pkt(RouterOut.ARBITER, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.ROUTER, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs)

async def test_loopback_inXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> input xbar -> arbiter -> spi.

    We expect the outputs' data to be the same as the inputs', their address bits
    might differ. We also prepend a message to inputs to configure the crossbar.
    """
    config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.IN_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs)

async def test_loopback_clsXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> classifier xbar -> arbiter -> spi.

    We expect the outputs' data to be the same as the inputs', their address
    bits might differ. We also prepend a message to inputs to configure the crossbar.
    """
    config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.CLS_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, msg) for msg in msgs]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs)

async def test_loopback_outXbar(dut, msgs):
    """
    Tests loopback route: spi -> router -> output xbar -> arbiter -> spi.

    We DON'T expect the outputs' data to be the same as the inputs'. We only 
    extract the least significant bit from the message since the output crossbar
    has an output bitwidth of 1. As usual, we also prepend a message to inputs to 
    configure the crossbar.
    """
    config_msg = mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.ROUTER_ARBITER)
    in_msgs = [config_msg] + [mk_spi_pkt(RouterOut.OUT_XBAR, msg) for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, msg & 1) for msg in msgs]  # output xbar only takes first bit

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs)

# Message values to pass into DUT for loopback tests
msgs_values = [
        [0xFFFF],
        [0x0000],
        [0x5555, 0xAAAA],
        [0xAAAA, 0x5555],
        [0xDEAD, 0xBEEF, 0xCAFE, 0xBABE],
        [0xABCD, 0x1234, 0x5678, 0x9ABC, 0xDEF0]
]

# Run tests with Cocotb test factory
if RUN_LOOPBACK_TESTS and RUN_SPI_TESTS:
    for test in [test_loopback_noXbar, test_loopback_inXbar, test_loopback_clsXbar, test_loopback_outXbar]:
        factory = TestFactory(test)
        factory.add_option("msgs", msgs_values)
        factory.generate_tests()


# FFT Tests -------------------------------------------------------------------
# Tests for:
# - spi -> router -> input xbar -> fft -> classifier xbar -> arbiter -> spi

def fixN(n):
    """Shortcut for creating fixed-point numbers."""
    return Fixed(n, True, 16, 8)

def fft_msg(inputs: list[Fixed], outputs: list[Fixed], fft_num, config=True):
    """Generate SPI packets for FFT input/output from fixed-point numbers."""

    assert fft_num in [1, 2]
    
    #ensure that input and output samples are converted from fixed to bits
    inputs = [fixed_bits(sample) for sample in inputs]
    outputs = [fixed_bits(sample) for sample in outputs]

    #configure input and output crossbars to send messages to/receive messages from FFT2
    if fft_num == 1:
        in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1)
        out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_ARBITER)
    else:
        in_xbar_config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT2)
        out_xbar_config_msg = mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_ARBITER)
    
    # send fft inputs to router and fft outputs to Arbiter from XBar
    in_msgs = [mk_spi_pkt(RouterOut.IN_XBAR, int(x)) for x in inputs]
    out_msgs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, int(x)) for x in outputs]

    #complete input and output message configurations
    if config:
        in_msgs = [in_xbar_config_msg, out_xbar_config_msg] + in_msgs
    
    return in_msgs, out_msgs

def test_fft_random_msg(dut, fft_num):
    random.seed(0xfeedbaba)
    input_mag = 2 ** 31
    input_num = 50

    inputs = [
        [
            CFixed((random.uniform(-2 ** 32, 2 ** 31 - 1), 0), 16, 8)
            for i in range(32)
        ]
        for _ in range(input_num)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    fft_inputs = []
    fft_outputs = []
    count = 0
    for _ in range(input_num):
        # while count < input_num:
        inputs = [
            CFixed((random.uniform(-input_mag, input_mag), 0), 16, 8)
            for i in range(32)
        ]
        # inputs = [[x.real for x in sample] for sample in inputs]
        outputs = model.transform(inputs)

        inputs = [x.real for x in inputs]
        outputs = [x.real for x in outputs][:16]
        outputs = [int(x.bin(), 2) for x in outputs]
        # dut._log.info(f"outputs: {[int(x.bin(), 2) for x in outputs]}")

        # outputs = [[x.real for x in sample][:16] for sample in outputs]
        # for o in outputs:
        #     if int(o) >> 16:
        #         break
        # else:

        fft_inputs.extend(inputs)
        fft_outputs.extend(outputs)
        count += 1
        # dut._log.info(f"We have {count} tests")

    # dut._log.info(f"We have {count} tests")

    assert count > 0

    # dut._log.info(f"{type(fft_inputs[0])}")
    # dut._log.info(f"{type(fft_outputs[0])}")

    if fft_num == 1:
        inputs = (
            [  # First, configure the crossbars
                mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1),
                mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_ARBITER),
            ]
            + [  # Finally, send the fft inputs
                mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for x in fft_inputs
                # int(fixed_bits(x)) for sample in fft_inputs for x in sample
            ]
        )
    else:
        inputs = (
            [  # First, configure the crossbars
                mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT2),
                mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_ARBITER),
            ]
            + [  # Finally, send the fft inputs
                mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for x in fft_inputs
                # int(fixed_bits(x)) for sample in fft_inputs for x in sample
            ]
        )

    # some random irrelevant message we can add for some delays
    # dummy = mk_spi_pkt(RouterOut.OUT_XBAR, OutXbarCfg.CLS_ARBITER)
    # for x in fft_inputs:
    #     inputs.append(mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))))
    #     for _ in range(random.randint(0, 3)):
    #         inputs.append(dummy)

    outputs = [mk_spi_pkt(ArbiterIn.CLS_XBAR, int(x)) for x in fft_outputs]

    return inputs, outputs
    # cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    # await reset_dut(dut)
    # await run_top(dut, inputs, outputs, max_trsns=3000)

async def test_fft1_manual(dut, input_output):
    inputs, outputs = input_output
    in_msgs, out_msgs = fft_msg(inputs, outputs, 1)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs, max_trsns=100)

async def test_fft1_random(dut):
    # input, output = input_output
    in_msgs, out_msgs = test_fft_random_msg(dut, 1)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs, max_trsns=3000)

async def test_fft2_manual(dut, input_output):
    inputs, outputs = input_output
    in_msgs, out_msgs = fft_msg(inputs, outputs, 2)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs, max_trsns=100)

async def test_fft2_random(dut):
    # input, output = input_output
    in_msgs, out_msgs = test_fft_random_msg(dut, 2)
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, in_msgs, out_msgs, max_trsns=3000)


# **Alternating FFT tests**
def gen_periodic(magnitude, period, n_samples):
    """
    Idea is:
    gen_periodic(4, 2, 8) would make [4, 0, 4, 0, 4, 0, 4, 0]
    gen_periodic(2, 1, 4) would make [2, 2, 2, 2]
    gen_periodic(1, 4, 4) would make [1, 0, 0, 0]
    """
    return [fixN(magnitude if x % period == 0 else 0) for x in range(n_samples)]

# Test Data
fft_io_values = [
    # ([[fixN(1) for _ in range(32)]], [[fixN(32)] + [fixN(0) for _ in range(15)]]),
    # ([[fixN(1 if x % 2 == 0 else 0) for x in range(32)]], [[fixN(1 if x % 16 == 0 else 0) for x in range(32)]]),
    # ([[fixN(1)] + [fixN(0) for _ in range(31)]], [[fixN(1) for _ in range(16)]]),

    (gen_periodic(1, 1, 32), gen_periodic(32, 32, 16)),  # 1, 1, 1, 1, ... -> 32, 0, 0, 0, ...
    (gen_periodic(1, 1, 32) + gen_periodic(1, 1, 32), gen_periodic(32, 32, 16) + gen_periodic(32, 32, 16)),  # 1, 1, 1, 1, ... -> 32, 0, 0, 0, ...
    (gen_periodic(1, 2, 32), gen_periodic(16, 16, 16)),  # 1, 0, 1, 0, ... -> 16, 0, 0, 0, 0, 0
    (gen_periodic(1, 4, 32), gen_periodic(8, 8, 16)),    # 1, 0, 0, 0, 1, 0, 0, 0, ... -> 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, ....
    (gen_periodic(1, 8, 32), gen_periodic(4, 4, 16)),    
    (gen_periodic(1, 16, 32), gen_periodic(2, 2, 16)),    
    (gen_periodic(1, 32, 32), gen_periodic(1, 1, 16)),   # 1, 0, 0, 0, ... -> 1, 1, 1, 1, ...
]


# Register test factory
if RUN_SPI_TESTS and RUN_FFT_TESTS:
    for test in [test_fft1_manual, test_fft2_manual]:
        factory = TestFactory(test)
        factory.add_option("input_output", fft_io_values)
        factory.generate_tests()

    for test in [test_fft1_random, test_fft2_random]:
        factory = TestFactory(test)
        factory.generate_tests()


# Classifier Tests ------------------------------------------------------------

# TODO

# FFT to Classifier -----------------------------------------------------------
async def test_fft_classifier_random(dut, input_mag, input_num, cutoff_freq, cutoff_mag, sampling_freq):
    inputs = [
        [
            CFixed((random.uniform(-input_mag, input_mag), 0), 16, 8)
            for i in range(32)
        ]
        for _ in range(input_num)
    ]

    model: FFTInterface = FFTPease(16, 8, 32)
    outputs = [model.transform(x) for x in inputs]

    fft_inputs = [[x.real for x in sample] for sample in inputs]
    fft_outputs = [[x.real for x in sample][:16] for sample in outputs]

    cutoff_mag = Fixed(cutoff_mag, True, 16, 8)

    params = [16,8, 16,16]
    classifier_output = classify(cutoff_freq, cutoff_mag, sampling_freq, fft_outputs[0], params)[0]

    inputs = (
        [  # First, configure the crossbars
            mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.ROUTER_FFT1),
            mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_CLS),
            mk_spi_pkt(RouterOut.OUT_XBAR_CTRL, OutXbarCfg.CLS_ARBITER),
        ]
        + [  # Next, configure the classifier
            mk_spi_pkt(RouterOut.CLS_CUT_FREQ_CTRL, cutoff_freq),
            mk_spi_pkt(RouterOut.CLS_MAG_CTRL, abs(int(cutoff_mag))),
            mk_spi_pkt(RouterOut.CLS_SAMP_FREQ_CTRL, sampling_freq),
        ]
        + [  # Finally, send the fft inputs
            mk_spi_pkt(RouterOut.IN_XBAR, int(fixed_bits(x))) for sample in fft_inputs for x in sample
            # int(fixed_bits(x)) for sample in fft_inputs for x in sample
        ]
    )

    outputs = [mk_spi_pkt(ArbiterIn.OUT_XBAR, classifier_output)]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, inputs, outputs, max_trsns=1000)



input_mag_values = [1, 10]
input_num_values = [1]
cutoff_freq_values = [0, 1000, 1400, 2000, 10000]
cutoff_mag_values = [0x0842, 0x7EAD, 0xC2FF]
sampling_freq_values = [44800, 25000, 0xffff]

if RUN_FFT_CLASSIFIER_TESTS and RUN_SPI_TESTS:
    for test in [test_fft_classifier_random]:
        factory = TestFactory(test)
        factory.add_option("input_mag", input_mag_values)
        factory.add_option("input_num", input_num_values)
        factory.add_option("cutoff_freq", cutoff_freq_values)
        factory.add_option("cutoff_mag", cutoff_mag_values)
        factory.add_option("sampling_freq", sampling_freq_values)
        factory.generate_tests()



# LBIST Tests -----------------------------------------------------------------
async def test_lbist_fft1(dut):
    input_msgs = []

    # Configure crossbars to send data along this path: LFSR -> FFT1 -> MISR
    input_msgs += [mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.LFSR_FFT1)]
    input_msgs += [mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT1_MISR)]

    # Send 1 to LBIST controller to start LBIST test
    input_msgs += [mk_spi_pkt(RouterOut.LBIST_CTRL, 1)]

    # Expect to receive an 8-bit integer of 1s, to signify 8 passed tests
    output_msgs = [mk_spi_pkt(ArbiterIn.LBIST_CTRL, 0b11111111)]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, input_msgs, output_msgs)

async def test_lbist_fft2(dut):
    input_msgs = []

    # Configure crossbars to send data along this path: LFSR -> FFT2 -> MISR
    input_msgs += [mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.LFSR_FFT2)]
    input_msgs += [mk_spi_pkt(RouterOut.CLS_XBAR_CTRL, ClsXbarCfg.FFT2_MISR)]

    # Send 1 to LBIST controller to start LBIST test
    input_msgs += [mk_spi_pkt(RouterOut.LBIST_CTRL, 1)]

    # Expect to receive an 8-bit integer of 1s, to signify 8 passed tests
    output_msgs = [mk_spi_pkt(ArbiterIn.LBIST_CTRL, 0b11111111)]

    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())
    await reset_dut(dut)
    await run_top_SPI(dut, input_msgs, output_msgs)

if RUN_SPI_TESTS and RUN_LBIST_TESTS:
    for test in [test_lbist_fft1, test_lbist_fft2]:
        factory = TestFactory(test)
        factory.generate_tests()


# =============================================================================
# ASync FIFO Tests 
# =============================================================================
# The following section defines the tests when driving the DUT with the ASync
# FIFO. To omit a set of tests, set its corresponding parameter to false in 
# the parameters section at the top.
#
# Ex: To omit the loopback tests for the ASync FIFO, set RUN_ASYNC_FIFO_TESTS = 
# False and RUN_LOOPBACK_TESTS = False
async def run_top(
    dut,
    in_msgs: list[int],
    out_msgs: list[int],
    max_trsns=30,
    curr_trsns=0,
    use_spi=1,
    num_config=0, peek=None
):
    """
    Run src/sink testing. src/snk msgs are converted to SPI protocol transactions.
    Testing is done at the transaction level.

    Args:
    dut: model for top
    in_msgs: a list of input messages
    out_msgs: a list of expected output messages
    max_trsns: the maximum number of transactions to run. test will fail if
      simulations take too long
    curr_trsns: the current transaction number (note from Tean: I've ported this
      over from previous testbenches for now, but I'm thinking of possibly removing it)
    peel: optional parameter to peek at the output messages (DO NOT REMOVE THIS - Johnny Martinez JJM469)
    """
    # SPI messages
    # dut._log.info(f"in_msgs = {in_msgs}")
    # dut._log.info(f"out_msgs = {out_msgs}")
    mk = mk_bits(SPI_PACKET_BITS)
    config_msgs = []
    in_msgs_fifo = []
    if use_spi:
        in_msgs = [mk(x) for x in in_msgs]
        out_msgs = [mk(x) for x in out_msgs]
    else:
        mk_fifo_config = mk_bits(8)
        config_msgs = [mk(x) for x in in_msgs[:num_config]]
        in_msgs_fifo = [mk_fifo_config(x) for x in in_msgs[num_config:]]
    # dut._log.info(f"config_msgs = {config_msgs}")
    # dut._log.info(f"in_msgs_fifo = {in_msgs_fifo}")
    in_idx = 0
    out_idx = 0
    trsns = curr_trsns + 1

    spc = 0

    # FIFO messages
    fifo_in = [int(x) for x in in_msgs_fifo]
    fifo_out = [int(x) for x in out_msgs]
    hex_fifo_in = [hex(i) for i in fifo_in]
    # dut._log.info(f"fifo_in = {hex_fifo_in}")

    # access FIFO submodule
    fifo = dut.async_fifo
    fifo_config_done = 0

    hex_fifo_out = [hex(i) for i in fifo_out]
    # dut._log.info(f"fifo_out = {hex_fifo_out}")
    # dut._log.info(f"use_spi = {use_spi}")

    while out_idx < len(out_msgs):
        if trsns > max_trsns:
            assert False, "Exceeded max transactions"

        # The following logging statements are for debugging purposes. Feel free
        # to modify them as needed.
        # dut._log.info("\nnew loop!")
        # dut._log.info(
        #     f"in_idx is {in_idx}, out_idx is {out_idx}, len(fifo_in): {len(fifo_in)}"
        # )
        # dut._log.info(f"spc = {spc}")
        # dut._log.info(
        #     f"router_2_clsxbar_val = {dut.Router_to_ClassifierXbar_val.value}"
        # )
        # dut._log.info(
        #     f"router_2_clsxbar_rdy = {dut.Router_to_ClassifierXbar_rdy.value}"
        # )

        # use SPI to send and receive data
        if use_spi:
            if in_idx < len(in_msgs) and spc == 1:
                spi_status, retmsg = await spi_write_read(dut, in_msgs[in_idx])

                # dut._log.info(
                #     f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}, sending in {hex(in_msgs[in_idx])}"
                # )
                spc = spi_status[0]

                if spi_status[1] == 1:
                    assert retmsg == out_msgs[out_idx]
                    out_idx += 1
                in_idx += 1

            else:
                spi_status, retmsg = await spi_read(dut)
                # dut._log.info(f"Trns {trsns}: {bin(spi_status)} | {hex(retmsg)}")
                spc = spi_status[0]
                if spi_status[1] == 1:
                    assert retmsg == out_msgs[out_idx]
                    out_idx += 1

        # use ASYNC FIFO to sent input data, router to send configuration messages, arbiter to receive messages
        else:

            # send in the SPI configuration messages for the path (only need to do this once!)
            if not fifo_config_done:
                # reset FIFO to 0
                fifo.async_rst.value = 0
                await ClockCycles(dut.clk, 1)

                for config_idx in range(len(config_msgs)):
                    spi_status, retmsg = await spi_write(dut, config_msgs[config_idx])
                    # dut._log.info(
                    #     f"[CONFIG] Sent {hex(config_msgs[config_idx])}, got {hex(retmsg)}"
                    # )

                # reset FIFO to 1
                fifo.async_rst.value = 1
                await ClockCycles(dut.clk, 1)

                # reset FIFO to 0
                fifo.async_rst.value = 0

                # This needs to be 4 cycles to allow for values to change in the reg file
                await ClockCycles(dut.clk, 4)
                # dut._log.info(f"[SPI CONFIG] Completed!")

                # only need to configure once
                fifo_config_done = 1

            # Send input FIFO msg if ready and haven't already sent current msg
            if fifo.istream_rdy.value == 1 and in_idx < len(fifo_in):
                # dut._log.info(f"[FIFO TX] Sending msg: {hex(fifo_in[in_idx] & 0xFF)}")
                fifo.istream_msg.value = fifo_in[in_idx] & 0xFF
                fifo.istream_val.value = 1
                await ClockCycles(dut.ext_clk, 2)
                in_idx += 1
                fifo.istream_val.value = 0
            else:
                await ClockCycles(dut.clk, 1)

            # wait for output from router
            spi_status, retmsg = await spi_read(dut)
            output_msg = mk(retmsg)
            # dut._log.info(f"SPI retmsg: {hex(output_msg)}")

            spc = spi_status[0]

            # if SPI minion is valid
            if spi_status[1] == 1:
                assert (
                    output_msg == out_msgs[out_idx]
                ), f"Output mismatch: got {hex(int(output_msg))}, expected {hex(int(out_msgs[out_idx]))}"
                # dut._log.info("[FIFO] Correct FIFO output message!")
                out_idx += 1

        trsns += 1

    return trsns - 1


# Loopback Tests --------------------------------------------------------------
async def test_fifo_loopback_inXbar(dut, msgs):
    """
    Tests loopback route: fifo -> packager -> input xbar -> arbiter -> spi.

    the input address is still configured by making SPI packets and setting ctrl bits through router
    since that's the only way of setting them.
    """
    config_msg = mk_spi_pkt(RouterOut.IN_XBAR_CTRL, InXbarCfg.FIFO_ARBITER)

    in_msgs = [config_msg] + [msg for msg in msgs]
    out_msgs = [mk_spi_pkt(ArbiterIn.IN_XBAR, (msg << 8)) for msg in msgs]

    cocotb.start_soon(Clock(dut.ext_clk, 2, "ns").start())  # input clk
    cocotb.start_soon(Clock(dut.clk, 1, "ns").start())  # output clk
    await reset_dut(dut)
    await run_top(dut, in_msgs, out_msgs, use_spi=0, num_config=1, max_trsns=70)

    # await run_top_AsyncFIFO(dut, in_msgs, out_msgs, num_config=1, max_trsns=32)



# FIFO only takes in 8-bit messages
fifo_msgs_values = [
    [0xFF, 0xFF],
    [0x00, 0x00],
    [0x55, 0x55, 0xAA, 0xAA],
    [0xAA, 0xAA, 0x55, 0x55],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xAB],
    [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE],
]

if RUN_ASYNC_FIFO_TESTS and RUN_LOOPBACK_TESTS:
    for test in [test_fifo_loopback_inXbar]:
        factory = TestFactory(test)
        factory.add_option("msgs", fifo_msgs_values)
        factory.generate_tests()

# LBIST Tests -----------------------------------------------------------------
