import pytest

from pymtl3 import *
from pymtl3.stdlib.test_utils import run_test_vector_sim
from src.router.harnesses.router import Router


def test_one(cmdline_opts):
    dut = Router(nbits=4, noutputs=2)
    # fmt: off
    run_test_vector_sim(dut,[
        ("istream_val istream_msg istream_rdy* ostream_val[0]* ostream_val[1]* ostream_msg[0]* ostream_msg[1]* ostream_rdy[0] ostream_rdy[1]"),
        [ 0x1,        0x1,        0x1,         0x0,            0x0,            0x0,            0x0,            0x0,         0x0], #1
        [ 0x1,        0x2,        0x1,         0x1,            0x0,            0x1,            0x1,            0x1,         0x1], #2
        [ 0x1,        0x3,        0x1,         0x1,            0x0,            0x2,            0x2,            0x1,         0x1], #3
        [ 0x1,        0x4,        0x1,         0x1,            0x0,            0x3,            0x3,            0x0,         0x0], #4
        [ 0x1,        0x4,        0x1,         0x1,            0x0,            0x3,            0x3,            0x1,         0x1], #5
        [ 0x1,        0x5,        0x1,         0x1,            0x0,            0x4,            0x4,            0x1,         0x1], #6
        [ 0x1,        0x8,        0x1,         0x1,            0x0,            0x4,            0x4,            0x1,         0x1], #7
        [ 0x1,        0x9,        0x1,         0x1,            0x0,            0x5,            0x5,            0x1,         0x1], #8
        [ 0x1,        0x0,        0x1,         0x0,            0x1,            0x8,            0x8,            0x1,         0x1], #9
    ],cmdline_opts)
    # fmt: on

    """
    Test Case 1 Explanation:
    Row 1: 1 is enqueued.
    Row 2: 2 is enqueued. 1 is dequeued with high valid bit at port 0. 
    Row 3: 3 is enqueued. 2 is dequeued with high valid bit at port 0. 
    Row 4: 4 is enqueued. 3 is dequeued with high valid bit at port 0. Successful enqueue but not a sucessful dequeue
    Row 5: 4 is enqueued. 4 is dequeued with high valid bit at port 0. 
    Row 6: 5 is enqueued. 4 is dequeued with high valid bit at port 0. 
    Row 7: 8 is enqueued. 4 is dequeued with high valid bit at port 0. 
    Row 8: 9 is enqueued. 8 is dequeued with high valid bit at port 1. 
    Row 9: 0 is enqueued. 9 is dequeued with high valid bit at port 1.
    """


# Tests standard router case w/ resets
def test_two(cmdline_opts):
    dut = Router(nbits=4, noutputs=2)
    # fmt: off
    run_test_vector_sim(dut,[
        ("istream_val istream_msg istream_rdy* ostream_val[0]* ostream_val[1]* ostream_msg[0]* ostream_msg[1]* ostream_rdy[0] ostream_rdy[1] reset"),
        [ 0x1,        0x1,        0x1,         0x0,            0x0,            0x0,            0x0,            0x0,         0x0,             0x0], #1
        [ 0x1,        0x2,        0x1,         0x1,            0x0,            0x1,            0x1,            0x1,         0x1,             0x0], #2
        [ 0x1,        0x3,        0x1,         0x1,            0x0,            0x2,            0x2,            0x1,         0x1,             0x1], #3
        [ 0x1,        0x8,        0x1,         0x0,            0x0,            0x0,            0x0,            0x1,         0x1,             0x0], #4
        [ 0x1,        0x8,        0x1,         0x0,            0x1,            0x8,            0x8,            0x1,         0x1,             0x0], #5
    ],cmdline_opts)
    # fmt: on

    """
    Test Case 2 Explanation: 
    Row 1: 1 is enqueued.
    Row 2: 2 is enqueued. 1 is dequeued with a high valid bit to port 0. 
    Row 3: The block is reset; 3 is not enqueued but 2 is dequeued to port 0. 
    Row 4: 8 is enqueued. No valid bits sent (post-reset).
    Row 5: 8 is enqueued. Valid bits sent to port 1. 
    """


# Tests router case where receiving ports are not ready
def test_three(cmdline_opts):
    dut = Router(nbits=4, noutputs=2)
    # fmt: off
    run_test_vector_sim(dut,[
        ("istream_val istream_msg istream_rdy* ostream_val[0]* ostream_val[1]* ostream_msg[0]* ostream_msg[1]* ostream_rdy[0] ostream_rdy[1] reset"),
        [ 0x1,        0x1,        0x1,         0x0,            0x0,            0x0,            0x0,            0x0,         0x0,             0x0], #1
        [ 0x1,        0x2,        0x1,         0x1,            0x0,            0x1,            0x1,            0x0,         0x1,             0x0], #2
        [ 0x1,        0x3,        0x1,         0x1,            0x0,            0x1,            0x1,            0x0,         0x0,             0x0], #3
        [ 0x0,        0x4,        0x0,         0x1,            0x0,            0x1,            0x1,            0x0,         0x0,             0x0], #4
    ],cmdline_opts)
    # fmt: on

    """
    Test Case 3 Explanation: 
    Row 1: 1 is enqueued. 
    Row 2: 2 is enqueued. 1 is dequeued with high valid bit to port 0. 
    Row 3: 3 is enqueued. 2 is not dequeued because port 0 is not ready to receive a message.
    Row 4: 4 is enqueued. Nothing is dequeued because port 0 is not ready to receive a message.
        * istream_rdy is also 0 because the router's queue is full. 
    """


# Tests standard router case with more than 2 ports.
def test_four(cmdline_opts):
    dut = Router(nbits=4, noutputs=4)
    # fmt: off
    run_test_vector_sim(dut,[
        ("istream_val istream_msg istream_rdy* ostream_val[0]* ostream_val[1]* ostream_val[2]* ostream_val[3]* ostream_msg[0]* ostream_msg[1]* ostream_msg[2]* ostream_msg[3]* ostream_rdy[0] ostream_rdy[1] ostream_rdy[2] ostream_rdy[3] reset"),
        [ 0x1,        0x1,        0x1,         0x0,            0x0,            0x0,            0x0,            0x0,            0x0,            0x0,            0x0,            0x0,         0x0,             0x0,            0x0,          0x0], #1
        [ 0x1,        0x7,        0x1,         0x1,            0x0,            0x0,            0x0,            0x1,            0x1,            0x1,            0x1,            0x1,         0x0,             0x0,            0x0,          0x0], #2
        [ 0x1,        0x8,        0x1,         0x0,            0x1,            0x0,            0x0,            0x7,            0x7,            0x7,            0x7,            0x0,         0x1,             0x0,            0x0,          0x0], #3
        [ 0x1,        0xf,        0x1,         0x0,            0x0,            0x1,            0x0,            0x8,            0x8,            0x8,            0x8,            0x0,         0x0,             0x1,            0x0,          0x0], #4
        [ 0x0,        0xf,        0x1,         0x0,            0x0,            0x0,            0x1,            0xf,            0xf,            0xf,            0xf,            0x0,         0x0,             0x0,            0x1,          0x0], #4
    ],cmdline_opts)
    # fmt: on

    """
    Test Case 4 Explanation: 
    Row 1: 1 is enqueued. 
    Row 2: 7 is enqueued. 1 is dequeued with high valid bit to port 0. 
    Row 3: 8 is enqueued. 7 is dequeued with high valid bit to port 1. 
    Row 4: 15 is enqueued. 8 is dequeued with high valid bit to port 2. 
    Row 5: Nothing enqueued. 15 dequeued with high valid bit to port 3.
    """
