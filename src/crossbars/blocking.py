# This is the PyMTL wrapper for the corresponding Verilog RTL model CrossbarVRTL.

from pymtl3 import *
from pymtl3.stdlib.stream.ifcs import RecvIfcRTL, SendIfcRTL
from pymtl3.passes.backends.verilog import *
from os import path
from tools.utils import mk_list_bitstruct


class BlockingCrossbar(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, BIT_WIDTH, N_INPUTS, N_OUTPUTS, CONTROL_BIT_WIDTH):
        s.set_metadata(VerilogTranslationPass.explicit_module_name, "crossbar")

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

        s.set_metadata(VerilogPlaceholderPass.top_module, "Blocking")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "blocking.v"),
        )


# Val/Rdy wrapper for the BlockingCrossbar
class BlockingCrossbarWrapper(Component):
    def construct(s, BIT_WIDTH, N_INPUTS, N_OUTPUTS, CONTROL_BIT_WIDTH):
        s.dut = BlockingCrossbar(BIT_WIDTH, N_INPUTS, N_OUTPUTS, CONTROL_BIT_WIDTH)

        s.recv = [RecvIfcRTL(BIT_WIDTH) for _ in range(N_INPUTS)]
        s.send = [SendIfcRTL(BIT_WIDTH) for _ in range(N_OUTPUTS)]
        s.control = RecvIfcRTL(mk_bits(CONTROL_BIT_WIDTH))

        s.control.msg //= s.dut.control
        s.control.val //= s.dut.control_val
        s.dut.control_rdy //= s.control.rdy

        for i in range(N_INPUTS):
            s.dut.recv_msg[i] //= s.recv[i].msg
            s.dut.recv_rdy[i] //= s.recv[i].rdy
            s.recv[i].val //= s.dut.recv_val[i]

        for i in range(N_OUTPUTS):
            s.send.msg.list[i] //= s.dut.send_msg[i]
            s.send[i].rdy //= s.dut.send_rdy[i]
            s.dut.send_val[i] //= s.send[i].val
