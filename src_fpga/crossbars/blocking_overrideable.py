# This is the PyMTL wrapper for the corresponding Verilog RTL model CrossbarVRTL.

from pymtl3 import *
from pymtl3.stdlib.stream.ifcs import RecvIfcRTL, SendIfcRTL
from pymtl3.passes.backends.verilog import *
from os import path
import math


class BlockingCrossbar(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, BIT_WIDTH, N_INPUTS, N_OUTPUTS):
        s.set_metadata(VerilogTranslationPass.explicit_module_name, "crossbar")

        CONTROL_BIT_WIDTH = int(math.log2(N_INPUTS) + math.log2(N_OUTPUTS))

        # Interface
        s.recv_msg = [InPort(mk_bits(BIT_WIDTH)) for _ in range(N_INPUTS)]
        s.recv_val = [InPort() for _ in range(N_INPUTS)]
        s.recv_rdy = [OutPort() for _ in range(N_INPUTS)]
        s.send_msg = [OutPort(mk_bits(BIT_WIDTH)) for _ in range(N_OUTPUTS)]
        s.send_val = [OutPort() for _ in range(N_OUTPUTS)]
        s.send_rdy = [InPort() for _ in range(N_OUTPUTS)]
        s.control = InPort(mk_bits(CONTROL_BIT_WIDTH))
        s.control_val = InPort(1)
        s.control_rdy = OutPort(1)
        s.input_override = InPort(1)
        s.output_override = InPort(1)
        s.set_metadata(VerilogPlaceholderPass.top_module, "BlockingOverrideable")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "blocking_overrideable.v"),
        )


# Val/Rdy wrapper for the BlockingCrossbar
class BlockingCrossbarWrapper(Component):
    def construct(s, BIT_WIDTH, N_INPUTS, N_OUTPUTS):
        s.dut = BlockingCrossbar(BIT_WIDTH, N_INPUTS, N_OUTPUTS)

        s.recv = [RecvIfcRTL(mk_bits(BIT_WIDTH)) for _ in range(N_INPUTS)]
        s.send = [SendIfcRTL(mk_bits(BIT_WIDTH)) for _ in range(N_OUTPUTS)]
        CONTROL_BIT_WIDTH = int(math.log2(N_INPUTS) + math.log2(N_OUTPUTS))
        s.control = RecvIfcRTL(mk_bits(CONTROL_BIT_WIDTH))

        s.input_override = RecvIfcRTL(mk_bits(1))
        s.output_override = RecvIfcRTL(mk_bits(1))

        s.control.msg //= s.dut.control
        s.control.val //= s.dut.control_val
        s.dut.control_rdy //= s.control.rdy

        s.input_override.msg //= s.dut.input_override
        s.input_override.rdy //= 1

        s.output_override.msg //= s.dut.output_override
        s.output_override.rdy //= 1

        for i in range(N_INPUTS):
            s.dut.recv_msg[i] //= s.recv[i].msg
            s.dut.recv_rdy[i] //= s.recv[i].rdy
            s.recv[i].val //= s.dut.recv_val[i]

        for i in range(N_OUTPUTS):
            s.send[i].msg //= s.dut.send_msg[i]
            s.send[i].rdy //= s.dut.send_rdy[i]
            s.dut.send_val[i] //= s.send[i].val
