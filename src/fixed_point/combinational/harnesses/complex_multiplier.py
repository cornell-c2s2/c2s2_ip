# -*- coding: utf-8 -*-
# @Author: UnsignedByte
# @Date:   2022-11-12 18:33:26
# @Last Modified by:   UnsignedByte
# @Last Modified time: 2022-11-12 18:33:48

from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


class ComplexMultiplierTestHarness(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n=32, d=16):
        # Interface

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(4 * n))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(2 * n))

        s.set_metadata(VerilogPlaceholderPass.top_module, "ComplexMultiplierHarness")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.dirname(__file__) + "/complex_multiplier.v",
        )
