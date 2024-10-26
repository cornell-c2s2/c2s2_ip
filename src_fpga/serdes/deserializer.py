from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from tools.utils import mk_list_bitstruct
from os import path


class Deserializer(VerilogPlaceholder, Component):
    # Constructor
    def construct(s, BIT_WIDTH, N_SAMPLES):
        # Interface
        s.recv_val = InPort()
        s.recv_rdy = OutPort()
        s.recv_msg = InPort(BIT_WIDTH)

        s.send_val = OutPort()
        s.send_rdy = InPort()
        s.send_msg = [OutPort(BIT_WIDTH) for _ in range(N_SAMPLES)]

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Deserializer")
        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "deserializer.v"),
        )


class DeserializerWrapper(Component):
    def construct(s, BIT_WIDTH, N_SAMPLES):
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(
            mk_list_bitstruct(mk_bits(BIT_WIDTH), N_SAMPLES)
        )

        s.dut = Deserializer(BIT_WIDTH, N_SAMPLES)

        s.recv.msg //= s.dut.recv_msg
        s.recv.val //= s.dut.recv_val
        s.dut.recv_rdy //= s.recv.rdy

        for i in range(N_SAMPLES):
            s.dut.send_msg[i] //= s.send.msg.list[i]
        s.dut.send_val //= s.send.val
        s.send.rdy //= s.dut.send_rdy

    def line_trace(s):
        return s.dut.line_trace()
