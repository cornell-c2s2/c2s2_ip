import os
import random
import sys
from pathlib import Path

import cocotb
from cocotb.triggers import Timer
from cocotb.runner import get_runner

@cocotb.test()
async def datapath_basic_test(dut):
    pass

@cocotb.test()
async def datapath_randomised_test(dut):
    pass

def test_datapath_runner():
    """Simulate the multiplier datapath using the Python runner.

        This file can be run directly or via pytest discovery.
    """
    hdl_toplevel_lang = os.getenv("HDL_TOPLEVEL_LANG", "verilog")
    sim = os.getenv("SIM", "icarus")

    proj_path = Path(__file__).resolve().parent.parent.parent.parent
    # equivalent to setting the PYTHONPATH environment variable
    sys.path.append(str(proj_path / "fixed_point" / "iterative" / "test_cocotb"))

    sources = [
       proj_path / "cmn" / "muxes.v",
       proj_path / "cmn" / "assert.v",
       proj_path / "cmn" / "regs.v",
       proj_path / "fixed_point" / "iterative" / "multiplier.v"
    ] 
    

    print(sources)
    build_test_args = []
    if hdl_toplevel_lang == "vhdl" and sim == "xcelium":
        build_test_args = ["-v93"]

    runner = get_runner(sim)
    runner.build(
        verilog_sources=sources,
        hdl_toplevel="FXPIterMultDatapath",
        always=True,
        build_args=build_test_args,
    )
    runner.test(
        hdl_toplevel="FXPIterMultDatapath", test_module="test_FXPIterMultDatapath", test_args=build_test_args
    )


if __name__ == "__main__":
    test_datapath_runner()