from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.serdes.deserializer import Deserializer
from src.serdes.serializer import Serializer
from src.fft.helpers.sine_wave import SineWave


# FFT
class FFT(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH, DECIMAL_PT, N_SAMPLES):
        # Interface
        s.recv_msg = [InPort(BIT_WIDTH) for _ in range(N_SAMPLES)]
        s.recv_val = InPort()
        s.recv_rdy = OutPort()

        s.send_msg = [OutPort(BIT_WIDTH) for _ in range(N_SAMPLES)]
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

        # Hook up a deserializer
        s.deserializer = Deserializer(BIT_WIDTH, N_SAMPLES)
        s.recv.msg //= s.deserializer.recv_msg
        s.recv.val //= s.deserializer.recv_val
        s.deserializer.recv_rdy //= s.recv.rdy

        # Hook up a serializer
        s.serializer = Serializer(BIT_WIDTH, N_SAMPLES)
        s.serializer.send_msg //= s.send.msg
        s.serializer.send_val //= s.send.val
        s.send.rdy //= s.serializer.send_rdy

        # Hook up the FFT
        s.dut = FFT(BIT_WIDTH, DECIMAL_PT, N_SAMPLES)

        # Hook up the deserializer to the FFT
        for i in range(N_SAMPLES):
            s.deserializer.send_msg[i] //= s.dut.recv_msg[i]

        s.deserializer.send_val //= s.dut.recv_val
        s.dut.recv_rdy //= s.deserializer.send_rdy

        # Hook up the FFT to the serializer
        for i in range(N_SAMPLES):
            s.dut.send_msg[i] //= s.serializer.recv_msg[i]

        s.dut.send_val //= s.serializer.recv_val
        s.serializer.recv_rdy //= s.dut.send_rdy

    def line_trace(s):
        return f"{s.deserializer.line_trace()} > {s.dut.line_trace()} > {s.serializer.line_trace()}"
