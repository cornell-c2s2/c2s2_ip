from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path


# Pymtl3 harness for the `Classifier` module.
class Classifier(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH, DECIMAL_PT, FREQ_BIT_WIDTH, N_SAMPLES):
        # Interface

        s.recv_msg = [InPort(BIT_WIDTH) for _ in range(N_SAMPLES)]
        s.recv_rdy = OutPort()
        s.recv_val = InPort()

        s.cutoff_freq = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.cutoff_mag = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.sampling_freq = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(1))

        # Name of the top level module to be imported
        s.set_metadata(VerilogPlaceholderPass.top_module, "Classifier")
        # Source file path
        # The ../ is necessary here because pytest is run from the build directory
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "classifier.v"),
        )
