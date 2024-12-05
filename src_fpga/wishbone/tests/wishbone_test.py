# =========================================================================
# RegArray_test
# =========================================================================

import pytest

from pymtl3 import DefaultPassGroup, Bits1
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3.stdlib.test_utils import config_model_with_cmdline_opts


from src.wishbone.wishbone import Wishbone

N = 0
R = 1
W = 2


# Helper function
def t(
    dut,
    wbs_fcn,
    wbs_dat_i,
    wbs_adr_i,
    wbs_dat_o,
    istream_rdy,
    istream_val,
    istream_data,
    ostream_rdy,
    ostream_val,
    ostream_data,
):

    # Write input value to input port
    for i in range(3):
        dut.ostream_data[i] @= ostream_data[i]
        dut.ostream_val[i] @= ostream_val[i]
        dut.istream_rdy[i] @= istream_rdy[i]

    if wbs_fcn == N:
        dut.wbs_stb_i @= 0
        dut.wbs_cyc_i @= 0
        dut.wbs_we_i @= 0
        dut.wbs_sel_i @= 0
    elif wbs_fcn == R:
        dut.wbs_stb_i @= 1
        dut.wbs_cyc_i @= 1
        dut.wbs_we_i @= 0
        dut.wbs_sel_i @= 0
    elif wbs_fcn == W:
        dut.wbs_stb_i @= 1
        dut.wbs_cyc_i @= 1
        dut.wbs_we_i @= 1
        dut.wbs_sel_i @= 0
    dut.wbs_dat_i @= wbs_dat_i
    dut.wbs_adr_i @= wbs_adr_i
    dut.sim_eval_combinational()

    for i in range(3):
        if istream_val[i] != "?":
            assert dut.istream_val[i] == istream_val[i]
        if istream_val[i] == Bits1(1) and istream_data[i] != "?":
            assert dut.istream_data[i] == istream_data[i]
        if ostream_rdy[i] != "?":
            assert dut.ostream_rdy[i] == ostream_rdy[i]

    assert dut.wbs_ack_o == 1

    if wbs_dat_o != "?":
        assert dut.wbs_dat_o == wbs_dat_o

    # Tick simulator one cycle
    dut.sim_tick()


# -------------------------------------------------------------------------
# test
# -------------------------------------------------------------------------


# Inject output data into each of 3 ports and read rdy
def test_check_ostream(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [1, 0, 0]) 
    t( dut,   R,    0,   0x3000_0018,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 1, 0],   [0, 1, 0]) 
    t( dut,   R,    0,   0x3000_0020,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 1],   [0, 0, 1]) 
    t( dut,   R,    0,   0x3000_0028,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # fmt: on


# Inject ostream data in all 3 queues at once
def test_check_ostream_parallel(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 1, 1],   [2, 2, 2]) 
    t( dut,   R,    0,   0x3000_0018,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   R,    0,   0x3000_0020,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   R,    0,   0x3000_0028,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # fmt: on


# Fill up ostream queue 0, check val, and read output
def test_fill_ostream_queue(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [0, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   R,    0,   0x3000_0018,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [0, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   R,    0,   0x3000_001c,    2,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [0, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])
    # fmt: on


# Write to istream, where each istream is rdy with varying delays
def test_check_istream(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   W,    5,   0x3000_0004,    0,     [1, 1, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [1, 0, 0],   [ 5, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [0, 0, 0],   [ 0, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    9,   0x3000_000c,    0,     [1, 0, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 0, 1],   [0, 1, 0],   ['?',  9,'?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [0, 1, 0],   ['?',  9,'?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [0, 0, 0],   ['?',  0,'?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    8,   0x3000_0014,    0,     [1, 1, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 0],   [0, 0, 1],   ['?','?',  8],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 0],   [0, 0, 1],   ['?','?',  8],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [0, 0, 1],   ['?','?',  8],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [0, 0, 0],   ['?','?',  0],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # fmt: on


# Fill istream queue then empty entire queue
def test_fill_istream_queue(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 1, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   W,    5,   0x3000_0004,    0,     [0, 1, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    6,   0x3000_0004,    0,     [0, 1, 1],   [1, 0, 0],   [ 5, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    7,   0x3000_0004,    0,     [0, 1, 1],   [1, 0, 0],   [ 5, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    8,   0x3000_0004,    0,     [0, 1, 1],   [1, 0, 0],   [ 5, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])  
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [1, 0, 0],   [ 5, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [1, 0, 0],   [ 6, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [1, 0, 0],   [ 7, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [1, 0, 0],   [ 8, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   N,    0,        0,         0,     [1, 1, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])
    # fmt: on


# Test istream queue correctly reports not ready when queue is full
def test_read_istream_rdy(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   R,    0,   0x3000_0000,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])  
    # fill up queue 0
    t( dut,   W,    5,   0x3000_0004,    0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    6,   0x3000_0004,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    7,   0x3000_0004,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    8,   0x3000_0004,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])
    # no longer ready because queue 0 full
    t( dut,   R,    0,   0x3000_0000,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # fmt: on


# Test writing to ostream val does nothing, outputs 0
def test_write_to_check_ostream(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # module 0 has output ready, sends into ostream queue 0
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [5, 0, 0]) 
    # try to write to val register
    t( dut,   W,    0,   0x3000_0018,    0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])
    # read from ostream queue 0 val register to confirm no change 
    t( dut,   R,    0,   0x3000_0018,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # fmt: on


# Test writing to istream rdy does nothing, outputs 0
def test_write_to_check_istream(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   R,    0,   0x3000_0000,    1,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])  
    # fill up queue 0
    t( dut,   W,    5,   0x3000_0004,    0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    6,   0x3000_0004,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    7,   0x3000_0004,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   W,    8,   0x3000_0004,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])
    # try to write to queue 0
    t( dut,   W,    1,   0x3000_0000,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])  
    # check that still no longer ready because queue 0 full
    t( dut,   R,    0,   0x3000_0000,    0,     [0, 0, 0],   [1, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # fmt: on


# Test writing to ostream does nothing, outputs 0
def test_write_to_ostream(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [1, 0, 0],   [2, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [0, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   W,    9,   0x3000_001c,    0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [0, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   R,    0,   0x3000_001c,    2,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [0, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   N,    0,        0,         0,     [0, 0, 0],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    # fmt: on


# Test reading to ostream does nothing, outputs 0
def test_read_from_istream(cmdline_opts):
    dut = Wishbone(4, 3, 3)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=True))

    # fmt: off
    dut.sim_reset()
    #        fcn  wb_dati  wbs_adr  wbs_dato*  istream_rdy  istream_val*  istream_data*  ostream_rdy*  ostream_val  ostream_data
    t( dut,   N,    0,        0,         0,     [0, 1, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0]) 
    t( dut,   W,    5,   0x3000_0004,    0,     [0, 1, 1],   [0, 0, 0],   ['?','?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])   
    t( dut,   R,    0,   0x3000_0004,    0,     [0, 1, 1],   [1, 0, 0],   [ 5, '?','?'],  [1, 1, 1],    [0, 0, 0],   [0, 0, 0])
    # fmt: on
