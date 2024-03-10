import pytest
import random
import math
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import mk_test_case_table, run_sim
from tools.utils import mk_packed
from src.classifier.classifier import Classifier
import numpy as np
from fixedpt import Fixed 

# ----------------------------------------------------------------------
# Helper Functions
# ----------------------------------------------------------------------
def make_fixed (n, d, v):
    max_fraction_value = 2**d
    scaled_number = round(v * max_fraction_value)
    return scaled_number

def make_arr_fixed (n, d, a):
    return [make_fixed(n, d, x) for x in a]

def pack_msg (n, arr):
    return mk_packed(n)(arr)

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, classifier, BIT_WIDTH=32, DECIMAL_PT = 16, N_SAMPLES = 8, CUTOFF_FREQ = 65536000, CUTOFF_MAG = 1310720, SAMPLING_FREQUENCY = 44000):
        # Instantiate models
        
        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH*N_SAMPLES))
        s.sink = stream.SinkRTL(mk_bits(1))
        s.classifier = classifier

        # Connect

        s.src.send //= s.classifier.recv
        s.classifier.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

def simple_test():
    audio_array = np.array([0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5])
    audio_array = audio_array - 0.5
    sample_rate = 50000
    frq_arr = np.fft.fft(audio_array)
    real_part = frq_arr.real
    return [real_part, 0]

test_case_table = mk_test_case_table(
    [
        (
                        "msgs        src_delay sink_delay BIT_WIDTH DECIMAL_PT N_SAMPLES CUTOFF_FREQ CUTOFF_MAG SAMPLING_FREQUENCY slow"
        ),
        ["simple_test", simple_test, 4,        4,         32,       16,        64,        65536000,   1310720,   50000,             False],
    ]
)

@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        Classifier(test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG, test_params.SAMPLING_FREQUENCY),
        test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG, test_params.SAMPLING_FREQUENCY
    )

    msgs = test_params.msgs()
    print(msgs)
    msgs = [make_arr_fixed(test_params.BIT_WIDTH, test_params.DECIMAL_PT, x) if i%2 != 0 else x for i, x in enumerate(msgs, start=1)]
    print(msgs)
    msgs = [mk_packed(test_params.BIT_WIDTH)(*x) if i%2 != 0 else x for i, x in enumerate(msgs, start=1)]
    print(msgs)

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

