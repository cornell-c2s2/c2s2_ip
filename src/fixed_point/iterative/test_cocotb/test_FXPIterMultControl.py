import pytest

import cocotb
from cocotb.triggers import Timer

import os
from pathlib import Path
import sys

from cocotb.runner import get_runner



# test_my_design.py (extended)

import cocotb
from cocotb.triggers import FallingEdge, Timer


async def generate_clock(dut):
    for cycle in range(50):
        dut.clk.value = 0
        await Timer(1, units="ns")
        dut.clk.value = 1
        await Timer(1, units="ns")

def is_idle(dut):
    tests = [
        (dut.in_wait.value, 1),
        (dut.do_add.value, 0),
        (dut.do_carry.value, 0),
        (dut.counter_reset.value, 0),
        (dut.recv_rdy.value, 1),
        (dut.send_val.value, 0)
    ]
    for actual, expected in tests:
        if actual != expected:
            return False
    return True

def is_done(dut):
    tests = [
        (dut.in_wait.value, 0),
        (dut.do_add.value, 0),
        (dut.do_carry.value, 0),
        (dut.counter_reset.value, 1),
        (dut.recv_rdy.value, 0),
        (dut.send_val.value, 1)
    ]
    for actual, expected in tests:
        if actual != expected:
            return False
    return True


@cocotb.test()
async def reset_test(dut):
    await cocotb.start(generate_clock(dut))
    await FallingEdge(dut.clk)
    dut.reset.value = 1
    await FallingEdge(dut.clk)
    tests = [
        (dut.in_wait.value, 1),
        (dut.do_add.value, 0),
        (dut.do_carry.value, 0),
        (dut.counter_reset.value, 0),
        (dut.recv_rdy.value, 1),
        (dut.send_val.value, 0)
    ]
    # for actual, expected in tests:
    #     assert actual == expected
    # assert False
    assert is_idle(dut)
    

@cocotb.test()
async def done_test(dut):
    await cocotb.start(generate_clock(dut))
    await Timer(40, 'ns')
    assert True
    # assert not is_done(dut)
    

    # for _ in range(15):
    #     await FallingEdge(dut)
    # assert is_done(dut)


def test_FXPIterMultControl_runner():
    hdl_toplevel_lang = os.getenv("HDL_TOPLEVEL_LANG", "verilog")
    sim = os.getenv("SIM", "icarus")

    print()
    proj_path = Path(__file__).resolve().parent.parent.parent.parent
    print("PATH IS:", proj_path)


    sys.path.append(str(proj_path / "fixed_point" / "iterative" / "test_cocotb"))

    includes = [
        proj_path
    ]

    build_args = ["-s", "FXPIterMultControl"]


    sources = [
       proj_path / "fixed_point" / "iterative" / "multiplier.v"
    ] 

    print("SOURCE IS:", sources)
    print()

    test_args = []

    runner = get_runner(sim)
    runner.build(
        # sources=sources,
        verilog_sources=sources,
        always=True,
        hdl_toplevel="FXPIterMultControl",
        includes=includes,
        build_args=build_args 
    )

    runner.test(
        hdl_toplevel="FXPIterMultControl", test_module="test_FXPIterMultControl", test_args=test_args
    )


if __name__ == "__main__":
    test_FXPIterMultControl_runner()