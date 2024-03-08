import pytest
import random
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from src.classifier.classifier import Classifier
import numpy as np

# ----------------------------------------------------------------------
# Helper Functions
# ----------------------------------------------------------------------

def extract_fft_arrays(audio_arr, sample_rate):
    fft_arr = np.fft.fft(audio_arr)
    frq_arr = np.fft.fftfreq(len(audio_arr), d=1/sample_rate)
    
    return fft_arr, frq_arr


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, classifier, BIT_WIDTH=32, DECIMAL_PT = 16, N_SAMPLES = 8, CUTOFF_FREQ = 65536000, CUTOFF_MAG = 1310720):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(N_SAMPLES*BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(1))
        s.classifier = classifier

        # Connect

        s.src.send //= s.distance_cal.recv
        s.distance_cal.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

def simple_test():
    audio_array = np.array([0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5])
    audio_array = audio_array - 0.5
    sample_rate = 50000
    fft_arr, frq_arr = extract_fft_arrays(audio_array, sample_rate)
    return [frq_arr, 0]

test_case_table = mk_test_case_table(
    [
        (
            "msgs        src_delay    sink_delay    BIT_WIDTH DECIMAL_PT N_SAMPLES CUTOFF_FREQ CUTOFF_MAG slow"
        ),
        ["simple_test", simple_test, 4, 4, 32, 16, 8, 65536000, 1310720, False],
    ]
)

@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        Classifier(test_params.BIT_WIDTH, test_params.F_BITS, test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG),
        test_params.BIT_WIDTH, test_params.F_BITS, test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG
    )

    msgs = test_params.msgs()

    th.set_param(
        "top.src.construct",
        msgs=msgs[::2],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=msgs[1::2],
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

    run_sim(th, cmdline_opts, duts=["classifier"])

