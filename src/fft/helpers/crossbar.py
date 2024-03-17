from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


# Crossbar Generator
class Crossbar(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH, SIZE_FFT, STAGE_FFT, FRONT):
        # Interface

        s.recv_real = [InPort(BIT_WIDTH) for _ in range(SIZE_FFT)]
        s.recv_imaginary = [InPort(BIT_WIDTH) for _ in range(SIZE_FFT)]
        s.recv_val = [InPort() for _ in range(SIZE_FFT)]
        s.recv_rdy = [OutPort() for _ in range(SIZE_FFT)]

        s.send_real = [OutPort(BIT_WIDTH) for _ in range(SIZE_FFT)]
        s.send_imaginary = [OutPort(BIT_WIDTH) for _ in range(SIZE_FFT)]
        s.send_val = [OutPort() for _ in range(SIZE_FFT)]
        s.send_rdy = [InPort() for _ in range(SIZE_FFT)]

        s.set_metadata(VerilogPlaceholderPass.top_module, "Crossbar")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "crossbar.v"),
        )
