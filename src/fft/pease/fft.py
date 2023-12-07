from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.serdes.deserializer import Deserializer
from src.serdes.serializer import Serializer
from src.fft.cooley_tukey.helpers.sine_wave import SineWave


# FFT
class FFT(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH, DECIMAL_PT, N_SAMPLES):
        # Interface
        s.recv_msg = InPort(BIT_WIDTH)
        s.recv_val = InPort()
        s.recv_rdy = OutPort()

        s.send_msg = OutPort(BIT_WIDTH)
        s.send_val = OutPort()
        s.send_rdy = InPort()

        s.set_metadata(VerilogPlaceholderPass.top_module, "FFT")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "fft.v"),
        )


class FFTWrapper(Component):
    def construct(s, BIT_WIDTH, DECIMAL_PT, N_SAMPLES):
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        s.dut = FFT(BIT_WIDTH, DECIMAL_PT, N_SAMPLES)

        s.recv.msg //= s.dut.recv_msg
        s.recv.val //= s.dut.recv_val
        s.dut.recv_rdy //= s.recv.rdy

        s.dut.send_msg //= s.send.msg
        s.dut.send_val //= s.send.val
        s.send.rdy //= s.dut.send_rdy

    def line_trace(s):
        return f"{s.dut.line_trace()}"
