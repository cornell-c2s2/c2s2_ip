import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from src.wishbone.harnesses.wishbone_adder import (
    WishboneAdderHarness,
)


# Creates a test harness class for the `Wishbone` module.
class Harness(Component):
    def construct(s, harness):
        s.harness = harness

        s.src = stream.SourceRTL(mk_bits(70))
        s.sink = stream.SinkRTL(mk_bits(33))

        s.src.send //= s.harness.recv
        s.harness.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# Initialize a simulatable model
def create_model():
    model = WishboneAdderHarness()

    # Create a harness wrapping our `Wishbone` module.
    return Harness(model)
# // recv_msg
# //     69          68        67       66:64      63:32     31:0
# // +----------+---------+---------+---------+----------+-----------+
# // wbs_stb_i  wbs_cyc_i  wbs_we_i  wbs_sel_i  wbs_dat_i  wbs_adr_i

# // wb -> proc
# // resp_msg
# //    32         31:0
# // +----------+---------+
# //  wbs_ack_o  wbs_dat_o
def gen_in(wbs_stb_i, wbs_cyc_i, wbs_we_i, wbs_sel_i, wbs_dat_i, wbs_adr_i):
    return wbs_adr_i | wbs_dat_i << 32 | wbs_sel_i << 64 | wbs_we_i << 67 | wbs_cyc_i << 68 | wbs_stb_i << 69

def gen_out(wbs_ack_o, wbs_dat_o):
    return wbs_dat_o | wbs_ack_o << 32
    


# def test_basic(): 
#     test_vals =  [
#             #wbs_stb_i | wbs_cyc_i | wbs_we_i | wbs_sel_i | wbs_dat_i |   wbs_adr_i     # wbs_ack_o,   wbs_dat_o
#             [gen_in(0,         0x0,         0,           0,          0,           0),     gen_out(0,          0)],
#             [gen_in(1,         0x1,         1,           0,        0x1,  0x3000_0000),    gen_out(1,          0)],
#             [gen_in(0,         0x0,         0,           0,          0,           0),     gen_out(0,          1)],
#             [gen_in(1,         0x1,         0,           0,          0,  0x3000_0000),    gen_out(1,        0x1)],
#             [gen_in(0,         0x0,         0,           0,          0,           0),     gen_out(0,          1)],]
#     inputs = [item[0] for item in test_vals]
#     outputs = [item[1] for item in test_vals]
#     return [inputs, outputs]

def test_adder_basic(): 
    test_vals =  [
            #      wbs_stb_i | wbs_cyc_i | wbs_we_i | wbs_sel_i | wbs_dat_i |   wbs_adr_i     # wbs_ack_o,   wbs_dat_o
            [gen_in(   0,         0x0,         0,           1,          0,           0),     gen_out(0,          0)],
            [gen_in(   1,         0x1,         1,           1,        0x1,  0x3000_0004),    gen_out(0,          0)],
            [gen_in(   0,         0x0,         0,           0,          0,           0),     gen_out(1,          0)], # BUSY
            [gen_in(   1,         0x1,         0,           0,          0,  0x3000_0004),    gen_out(1,        0x2)],
            [gen_in(0,         0x0,         0,           0,          0,           0),     gen_out(0,          0)],
            ]
    inputs = [item[0] for item in test_vals]
    outputs = [item[1] for item in test_vals]
    return [inputs, outputs]


@pytest.mark.parametrize(
    "f",
    [
        # (test_basic),
        (test_adder_basic)
    ],
)
def test_wb(request, f):
    # The name of the test function run
    test_name = request.node.name
    # Create our model.
    model = create_model()
    model.set_param(
        "top.src.construct",
        # Input values to stream through the block in order
        msgs=f()[0],
        # Cycles to wait after reset before starting to send inputs
        initial_delay=1,
        # Cycles to wait before sending next input (before `send_val` set high)
        interval_delay=0,
    )
    model.set_param(
        "top.sink.construct",
        # Expected output values to read from the block in order
        msgs=f()[1],
        # Cycles to wait after reset before setting `recv_rdy` to high
        initial_delay=1,
        # Cycles to wait between outputs before setting `recv_rdy` to high
        interval_delay=0,
    )
    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            # Creates the vcd file test_simple_<n_modules>.vcd for debugging.
            "dump_vcd": f"{test_name}",
            # Optional, used to test accurate cycle counts.
            "max_cycles": None,
        },
    )
