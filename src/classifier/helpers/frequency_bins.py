from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from os import path


# Frequency bin generator
class FrequencyBins(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, N_SAMPLES, BIT_WIDTH):
        # Interface

        s.sampling_freq = InPort(BIT_WIDTH)
        s.frequency_out = [OutPort(BIT_WIDTH) for _ in range(N_SAMPLES)]

        s.set_metadata(VerilogPlaceholderPass.top_module, "FrequencyBins")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "frequency_bins.v"),
        )
