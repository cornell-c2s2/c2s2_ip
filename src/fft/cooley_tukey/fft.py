from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.serdes.deserializer import Deserializer
from src.serdes.serializer import Serializer


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
