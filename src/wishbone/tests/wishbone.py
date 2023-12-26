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

        s.src = stream.SourceRTL(mk_bits(71+32*n+2*n))
        s.sink = stream.SinkRTL(mk_bits(32*(n-1)+31 + 33+2*n+1))

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
    return addr | dat << 32 | sel << 64 | we << 68 | cyc << 69 | stb << 70 |ostream_dat << 71 | val << 71+32*n_modules | rdy << 71+32*n_modules+n_modules

def gen_out(n_modules, dat, istream_dat, ack, val, rdy):
    return dat | ack << 32 | val << 33 | rdy << 33 + n_modules | istream_dat << 33+2*n_modules

def gen_dat(in1, in0):
    return in0 | in1 << 32

def gen_vr(in1, in0):
    return in0 | in1 << 1

def err_i(n):
    return gen_in(1,0x3000_0004, 0x0,           0,   0,  0,   1,   1,   0,   0) #read error reg

def nerr_o(n):
    return gen_out(n,    0,           0,   1,   0,   0)  # read error reg

def err_o(n):
    return gen_out(n,    1,           0,   1,   0,   0)  # read error reg
    
def loop_in(n): 
    return [
        #                                                              ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        #testing loopback
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,0x3000_0000, 0x4,           0,   0,  1,   1,   1,   0,   0), #write to loop
        err_i(n), #read error reg
        gen_in(n,0x3000_0000, 0x0,           0,   0,  0,   1,   1,   0,   0), #read from loop
        err_i(n), #read error reg
        ]

def loop_out(n):
    return [
        #                                     istream ostream
        # n_modules,  dat, istream_dat, ack, val, rdy
        # testing loopback
        gen_out(n,    0,           0,   0,   0,   0),
        gen_out(n,   0x0,  gen_dat(0x4,0x4),   1,   0,   0), # write to loop
        nerr_o(n),  # read error reg
        gen_out(n,   0x4,       0x0,   1,   0,   0), # read from loop
        nerr_o(n), # read error reg
        ]
    
    
def loop_delay_in(n): 
    return [
        #                                                              ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        #testing loopback delay
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,0x3000_0000, 0xffff,        0,   0,  1,   1,   1,   0,   0),
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,0x3000_0000, 0x0,           0,   0,  0,   1,   1,   0,   0),

        ]
def loop_delay_out(n):
    return [
        #                                     istream ostream
        #  n_modules,  dat, istream_dat, ack, val, rdy
       # testing loopback delay
        gen_out(n,    0,           0,   0,   0,   0),
        gen_out(n,   0x0,       gen_dat(0xffff, 0xffff),   1,   0,   0),
        gen_out(n, 0xffff,           0,   0,   0,   0),
        gen_out(n, 0xffff,           0,   0,   0,   0),
        gen_out(n, 0xffff,           0,   0,   0,   0),
        gen_out(n, 0xffff,         0x0,   1,   0,   0),     
        
        ]
    
def write_read_module0_in(n): 
    return [
        #                                                        ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   1),
        gen_in(n,0x3000_0008, 0x4,           0,   0,  1,   1,   1,   0,   1), # write to module 0
        err_i(n), #read error reg
        gen_in(n,0x3000_0008, 0x0,         0x4,   0,  0,   0,   0,   1,   0),
        gen_in(n,0x3000_0008, 0x0,         0x4,   0,  0,   1,   1,   1,   0),
        err_i(n), #read error reg
        ]
    
def write_read_module0_out(n):
    return [
        #                                     istream ostream
        #n_modules,  dat,      istream_dat, ack, val, rdy
        gen_out(n,    0,                 0,   0,   0,   0),
        gen_out(n,   0x0, gen_dat(0x4,0x4),   1,   1,   0),
        nerr_o(n), # read error reg
        gen_out(n,   0x0,              0x0,   0,   0,   0),
        gen_out(n,   0x4,              0x0,   1,   0,   1),
        nerr_o(n), # read error reg
        ]

def write_read_module1_in(n): 
    return [
        #                                                              ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb,         val, rdy
        gen_in(n,        0x0,   0,             0,   0,  0,   0,    0,           0,  gen_vr(1,1)),
        gen_in(n,0x3000_000c, 0x4,             0,   0,  1,   1,    1,           0,  gen_vr(1,1)), # write to module 1
        err_i(n),
        gen_in(n,0x3000_000c, 0x0, gen_dat(0x4,0),   0,  0,   0,   0, gen_vr(1,0),            0),
        gen_in(n,0x3000_000c, 0x0, gen_dat(0x4,0),   0,  0,   1,   1, gen_vr(1,0),            0),
        err_i(n),
        ]
    
def write_read_module1_out(n):
    return [
        #                                            istream ostream
        #n_modules,  dat,      istream_dat, ack,         val, rdy
        gen_out(n,    0,                 0,   0,           0,           0),
        gen_out(n,   0x0, gen_dat(0x4,0x4),   1, gen_vr(1,0),           0),
        nerr_o(n), 
        gen_out(n,   0x0,              0x0,   0,           0,           0),
        gen_out(n,   0x4,              0x0,   1,           0, gen_vr(1,0)),
        nerr_o(n),
        ]
    
def mixed_write_read_in(n): 
    return [
        #                                                                     ostream          istream
        # n_modules,    addr, dat,      ostream_dat, sel, we, cyc, stb,          val,           rdy
        gen_in(n,        0x0,   0,                0,   0,  0,   0,   0,           0,  gen_vr(1,1)),
        gen_in(n,0x3000_000c, 0x4,                0,   0,  1,   1,   1,           0,  gen_vr(1,1)), # write to module 1
        err_i(n),
        gen_in(n,0x3000_0008, 0x8,   gen_dat(0x4,0),   0,  1,   1,   1, gen_vr(1,0),  gen_vr(0,1)), # write to module 0
        err_i(n),
        gen_in(n,0x3000_000c, 0x0, gen_dat(0x4,0x8),   0,  0,   1,   1, gen_vr(1,1),  gen_vr(0,0)), #read module 1
        err_i(n),
        gen_in(n,0x3000_0008, 0x0, gen_dat(0x4,0x8),  0,  0,    1,    1, gen_vr(0,1),  gen_vr(1,0)), #read module 0
        err_i(n),
        ]
    
def mixed_write_read_out(n):
    return [
        #                                            istream        ostream
        #n_modules,  dat,      istream_dat, ack,         val,          rdy
        gen_out(n,    0,                 0,   0,           0,           0),
        gen_out(n,   0x0, gen_dat(0x4,0x4),   1, gen_vr(1,0),           0), # write to module 1
        nerr_o(n), 
        gen_out(n,   0x0, gen_dat(0x8,0x8),   1, gen_vr(0,1),           0), # write to module 0
        nerr_o(n),
        gen_out(n,   0x4,              0x0,   1,           0, gen_vr(1,0)), #read module 1
        nerr_o(n),
        gen_out(n,   0x8,              0x0,   1,           0, gen_vr(0,1)), #read module 0
        nerr_o(n),
        ]

def write_err_in(n): 
    return [
        #                                                        ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,0x3000_0008, 0x4,           0,   0,  1,   1,   1,   0,   gen_vr(1,0)), # write to module 0
        err_i(n), 
        gen_in(n,0x3000_000c, 0x8,           0,   0,  1,   1,   1,   0,   gen_vr(0,1)), # write to module 0
        err_i(n),
        ]
    
def write_err_out(n):
    return [
        #                                     istream ostream
        #n_modules,  dat,      istream_dat, ack, val, rdy
        gen_out(n,    0,                 0,   0,   0,   0),
        gen_out(n,   0x0, gen_dat(0x4,0x4),   1,   0,   0),
        err_o(n), # read error reg
        gen_out(n,   0x0, gen_dat(0x8,0x8),   1,   0,   0),
        err_o(n), # read error reg
        ]
    
def read_err_in(n): 
    return [
        #                                                        ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,0x3000_000c,   0,           0,   0,  0,   1,   1,   0,   gen_vr(1,0)), # read to module 1
        err_i(n), 
        gen_in(n,0x3000_0008,   0,           0,   0,  0,   1,   1,   0,   gen_vr(0,1)), # read to module 0
        err_i(n),
        ]
    
def read_err_out(n):
    return [
        #                                     istream ostream
        #n_modules,  dat,      istream_dat, ack, val, rdy
        gen_out(n,    0,                 0,   0,   0,   0),
        gen_out(n,   0x0,                0,   1,   0,   0),
        err_o(n), # read error reg
        gen_out(n,   0x0,                0,   1,   0,   0),
        err_o(n), # read error reg
        ]

def read_stall_m0_in(n):
    return [
        #                                                        ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,0x3000_0008,   0,           0,   0,  1,   1,   1,   0,   gen_vr(0,1)), # write to module 0
        err_i(n), 
        gen_in(n,0x3000_0008,   0,           0,   0,  0,   1,   1,   0,   0), # read to module 0
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0), # stall 1
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0), # stall 2
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0), # stall 3
        gen_in(n,        0x0,   0,         0xF,   0,  0,   0,   0,   1,   0), # output valid
        # err_i(n), 
        ]
    
def read_stall_m0_out(n):
    return [
        #                                     istream ostream
        #n_modules,  dat,      istream_dat, ack, val, rdy
        gen_out(n,    0,                 0,   0,   0,   0),
        gen_out(n,   0x0,                0,   1,   1,   0),
        nerr_o(n), # read error reg
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0xF,                0,   1,   0,   1),
        # nerr_o(n), # read error reg
        ]
    
def read_stall_m1_in(n):
    return [
        #                                                        ostream istream
        # n_modules,    addr, dat, ostream_dat, sel, we, cyc, stb, val, rdy
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0),
        gen_in(n,0x3000_000c,   0,           0,   0,  1,   1,   1,   0,   gen_vr(1,0)), # write to module 0
        err_i(n), 
        gen_in(n,0x3000_000c,   0,           0,   0,  0,   1,   1,   0,   0), # read to module 0
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0), # stall 1
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0), # stall 2
        gen_in(n,        0x0,   0,           0,   0,  0,   0,   0,   0,   0), # stall 3
        gen_in(n,        0x0,   0, gen_dat(0xF,0),0,  0,   0,   0,gen_vr(1,0),   0), # output valid
        # err_i(n), 
        ]
    
def read_stall_m1_out(n):
    return [
        #                                     istream ostream
        #n_modules,  dat,      istream_dat, ack, val, rdy
        gen_out(n,    0,                 0,   0,   0,   0),
        gen_out(n,   0x0,                0,   1, gen_vr(1,0), 0),
        nerr_o(n), # read error reg
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0x0,                0,   0,   0,   0),
        gen_out(n,   0xF,                0,   1,   0,   gen_vr(1,0)),
        # nerr_o(n), # read error reg
        ]
    
# TODO: read stall, mixed read stall with various stall
# TODO: (non)mixed write, read stall
#       (non)mixed write error, read error

@pytest.mark.parametrize(
    "n_modules, f_in, f_out",
    [
        (2, loop_in, loop_out),
        (2, loop_delay_in, loop_delay_out),
        (2, write_read_module0_in, write_read_module0_out),
        (2, write_read_module1_in, write_read_module1_out),
        (2, mixed_write_read_in, mixed_write_read_out),
        (2, write_err_in, write_err_out),
        (2, read_err_in, read_err_out),
        (2, read_stall_m0_in, read_stall_m0_out),
        (2, read_stall_m1_in, read_stall_m1_out),
        # (1, test_fft_in, test_fft_out),
        # (1, test_fft_delay_in, test_fft_delay_out),
    ],
)
def test_wb(request, n_modules, f_in, f_out):
    # The name of the test function run
    test_name = request.node.name
    # Create our model.
    model = create_model(n_modules)
    model.set_param(
        "top.src.construct",
        # Input values to stream through the block in order
        msgs=f_in(n_modules),
        # Cycles to wait after reset before starting to send inputs
        initial_delay=1,
        # Cycles to wait before sending next input (before `send_val` set high)
        interval_delay=1,
    )
    model.set_param(
        "top.sink.construct",
        # Expected output values to read from the block in order
        msgs=f_out(n_modules),
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
