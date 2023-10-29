import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from src.wishbone.harnesses.wishbone import (
    WishboneHarness,
)


# Creates a test harness class for the `Wishbone` module.
class Harness(Component):
    def construct(s, harness, n):
        s.harness = harness

        s.src = stream.SourceRTL(mk_bits(103+2*n))
        s.sink = stream.SinkRTL(mk_bits(65+2*n))

        s.src.send //= s.harness.recv
        s.harness.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# Initialize a simulatable model
def create_model(n):
    model = WishboneHarness(n)

    # Create a harness wrapping our `Wishbone` module.
    return Harness(model, n)

def gen_in(n_modules, addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy):
    return addr | dat << 32 | ostream_dat << 64 | sel << 96 | we << 100 | cyc << 101 | stb << 102 | val << 103 | rdy << 103 + n_modules

def gen_out(n_modules, dat, istream_dat, ack, val, rdy):
    return Bits67(dat | istream_dat << 32 | ack << 64 | val << 65 | rdy << 65 + n_modules)

def test_loop_in(): 
    return [
        #                                                              ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        #testing loopback
        gen_in(1,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,0x3000_0000, 0x4,           0,   0,  1,   1,   1,   0,   0),
        gen_in(1,0x3000_0000, 0x0,           0,   0,  0,   1,   1,   0,   0)
        ]
def test_loop_out():
    return [
        #                                     istream ostream
        #       n_modules,  dat, istream_dat, ack, val, rdy
        # testing loopback
        gen_out(1,    0,           0,   0,   0,   0),
        gen_out(1,   0x0,       0x4,   1,   0,   0),
        gen_out(1,   0x4,       0x0,   1,   0,   0)
        ]
    
    
def test_loop_delay_in(): 
    return [
        #                                                              ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        #testing loopback delay
        gen_in(1,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,0x3000_0000, 0xffff,        0,   0,  1,   1,   1,   0,   0),
        gen_in(1,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,0x3000_0000, 0x0,           0,   0,  0,   1,   1,   0,   0),

        ]
def test_loop_delay_out():
    return [
        #                                     istream ostream
        #       n_modules,  dat, istream_dat, ack, val, rdy
       # testing loopback delay
        gen_out(1,    0,           0,   0,   0,   0),
        gen_out(1,   0x0,       0xffff,   1,   0,   0),
        gen_out(1,    0,           0,   0,   0,   0),
        gen_out(1,    0,           0,   0,   0,   0),
        gen_out(1,    0,           0,   0,   0,   0),
        gen_out(1,   0xffff,     0x0,   1,   0,   0),     
        
        ]
    
def test_fft_in(): 
    return [
        #                                                        ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        gen_in(1,        0x0,   0,           0,   0,  0,   0,   0,   0,   1),
        gen_in(1,0x3000_0004, 0x4,           0,   0,  1,   1,   1,   0,   1),
        gen_in(1,0x3000_0004, 0x0,         0x4,   0,  0,   0,   0,   1,   0),
        gen_in(1,0x3000_0004, 0x0,         0x4,   0,  0,   1,   1,   1,   0)
        ]
def test_fft_out():
    return [
        #                                istream ostream
        #n_modules,  dat, istream_dat, ack, val, rdy
        gen_out(1,    0,           0,   0,   0,   0),
        gen_out(1,   0x0,        0x4,   0,   1,   0),
        gen_out(1,   0x4,        0x0,   1,   0,   0),
        gen_out(1,   0x4,        0x0,   1,   0,   1)
        ]

def test_fft_delay_in(): 
    return [
        #                                                        ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        gen_in(1,        0x0,   0,           0,   0,  0,   0,   0,   0,   1),
        gen_in(1,0x3000_0004, 0xffff,        0,   0,  1,   1,   1,   0,   1),
        gen_in(1,0x3000_0004, 0x0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,0x3000_0004, 0x0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,0x3000_0004, 0x0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(1,0x3000_0004, 0x0,      0xffff,   0,  0,   0,   0,   1,   0),
        gen_in(1,0x3000_0004, 0x0,      0xffff,   0,  0,   1,   1,   1,   0)
        ]
def test_fft_delay_out():
    return [
        #                                istream ostream
        #n_modules,  dat, istream_dat, ack, val, rdy
        gen_out(1,    0,            0,   0,   0,   0),
        gen_out(1,   0x0,      0xffff,   0,   1,   0),
        gen_out(1,   0x0,           0,   0,   0,   0),
        gen_out(1,   0x0,           0,   0,   0,   0),
        gen_out(1,   0x0,           0,   0,   0,   0),
        gen_out(1,   0xffff,        0,   1,   0,   0),
        gen_out(1,   0xffff,        0,   1,   0,   1)
        ]

@pytest.mark.parametrize(
    "n_modules",
    [
        (1),
    ],
)
def test_loop(request, n_modules):
    # The name of the test function run
    test_name = request.node.name
    # Create our model.
    model = create_model(n_modules)
    model.set_param(
        "top.src.construct",
        # Input values to stream through the block in order
        msgs=test_loop_in(),
        # Cycles to wait after reset before starting to send inputs
        initial_delay=1,
        # Cycles to wait before sending next input (before `send_val` set high)
        interval_delay=1,
    )
    model.set_param(
        "top.sink.construct",
        # Expected output values to read from the block in order
        msgs=test_loop_out(),
        # Cycles to wait after reset before setting `recv_rdy` to high
        initial_delay=1,
        # Cycles to wait between outputs before setting `recv_rdy` to high
        interval_delay=1,
    )
    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            # Creates the vcd file test_simple_<n_modules>.vcd for debugging.
            "dump_vcd": f"{test_name}_{n_modules}",
            # Optional, used to test accurate cycle counts.
            "max_cycles": None,
        },
    )
    
def test_loop_delay(request):
    test_name = request.node.name
    model = create_model(1)
    model.set_param(
        "top.src.construct",
        msgs=test_loop_delay_in(),
        initial_delay=1,
        interval_delay=1,
    )
    model.set_param(
        "top.sink.construct",
        msgs=test_loop_delay_out(),
        initial_delay=1,
        interval_delay=1,
    )
    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            "dump_vcd": f"{test_name}_{1}",
            "max_cycles": None,
        },
    )
def test_fft(request):
    test_name = request.node.name
    model = create_model(1)
    model.set_param(
        "top.src.construct",
        msgs=test_fft_in(),
        initial_delay=1,
        interval_delay=1,
    )
    model.set_param(
        "top.sink.construct",
        msgs=test_fft_out(),
        initial_delay=1,
        interval_delay=1,
    )
    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            "dump_vcd": f"{test_name}_{1}",
            "max_cycles": None,
        },
    )
def test_fft_delay(request):
    test_name = request.node.name
    model = create_model(1)
    model.set_param(
        "top.src.construct",
        msgs=test_fft_delay_in(),
        initial_delay=1,
        interval_delay=1,
    )
    model.set_param(
        "top.sink.construct",
        msgs=test_fft_delay_out(),
        initial_delay=1,
        interval_delay=1,
    )
    run_sim(
        model,
        cmdline_opts={
            "dump_textwave": False,
            "dump_vcd": f"{test_name}_{1}",
            "max_cycles": None,
        },
    )
