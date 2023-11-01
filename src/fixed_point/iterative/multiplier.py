from pymtl3 import mk_bits, InPort, OutPort, Component
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.fixed_point.utils import mk_multiplier_input, mk_multiplier_output


# Pymtl3 harness for the `FixedPointIterativeMultiplier` module.
class Multiplier(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, n, d):
        # Interface
        s.a = InPort(mk_bits(n))
        s.b = InPort(mk_bits(n))

        s.c = OutPort(mk_bits(n))

        s.recv_val = InPort()
        s.recv_rdy = OutPort()
        s.send_val = OutPort()
        s.send_rdy = InPort()

        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "multiplier.v"),
        )

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Multiplier")


class MultiplierWrapper(Component):
    def construct(s, n, d):
        s.dut = Multiplier(n, d)
        s.recv = stream.ifcs.RecvIfcRTL(mk_multiplier_input(n))
        s.recv.msg.a //= s.dut.a
        s.recv.msg.b //= s.dut.b

        s.recv.val //= s.dut.recv_val
        s.dut.recv_rdy //= s.recv.rdy
        s.send = stream.ifcs.SendIfcRTL(mk_multiplier_output(n))
        s.dut.c //= s.send.msg.c

        s.dut.send_val //= s.send.val
        s.send.rdy //= s.dut.send_rdy
