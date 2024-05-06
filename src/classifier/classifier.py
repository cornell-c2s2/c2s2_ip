from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path

class Classifier(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH, N_SAMPLES):
        # Interface
        s.recv_msg = [InPort(BIT_WIDTH) for _ in range(N_SAMPLES)]
        s.recv_val = InPort()
        s.recv_rdy = OutPort()

        s.send_msg = OutPort()
        s.send_val = OutPort()
        s.send_rdy = InPort()

        s.set_metadata(VerilogPlaceholderPass.top_module, "Classifier")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "classifier_v2.v"),
        )
