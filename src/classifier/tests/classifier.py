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
from src.classifier.classifier import ClassifierWrapper
import numpy as np
from fixedpt import Fixed 
import wave

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

def read_wav_file(file_path):
    with wave.open(file_path, 'rb') as wav_file:
        audio_data = wav_file.readframes(-1)
        audio_array = np.frombuffer(audio_data, dtype=np.int16)
        sample_rate = wav_file.getframerate()
        num_channels = wav_file.getnchannels()

    return audio_array, sample_rate, num_channels

# Cast a Fixed object to a Bits object
def fixed_bits(f: Fixed) -> Bits:
    value = f.get()

    return mk_bits(len(f))(value)

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, classifier, BIT_WIDTH=32, DECIMAL_PT = 16, N_SAMPLES = 8, CUTOFF_FREQ = 65536000, CUTOFF_MAG = 1310720, SAMPLING_FREQUENCY = 44000):
        # Instantiate models
        
        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(1))
        s.classifier = ClassifierWrapper(BIT_WIDTH, DECIMAL_PT, N_SAMPLES, CUTOFF_FREQ, CUTOFF_MAG, SAMPLING_FREQUENCY)

        # Connect

        s.src.send //= s.classifier.recv
        s.classifier.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

def false_test():
    audio_array = np.array([0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5,0,0.5,1,0.5])
    audio_array = audio_array - 0.5
    sample_rate = 50000
    frq_arr = np.fft.fft(audio_array)
    real_part = frq_arr.real
    return [real_part, 0]

def true_test():
    file_path = '/home/tic3/c2s2_ip/src/classifier/audio_files/ABS_MCBY_-YWX_MixPre-672.WAV'
    audio_array, sample_rate, num_channels = read_wav_file(file_path)
    audio_array_0 = audio_array[:64]
    audio_array_1 = audio_array[64:128]
    audio_array_2 = audio_array[128:192]
    audio_array_3 = audio_array[192:256]
    frq_arr = np.fft.fft(audio_array_0)
    real_part = frq_arr.real
    return [real_part, 1]


test_case_table = mk_test_case_table(
    [
        (
                        "msgs        src_delay sink_delay BIT_WIDTH DECIMAL_PT N_SAMPLES CUTOFF_FREQ CUTOFF_MAG SAMPLING_FREQUENCY slow"
        ),
        #["false_test",   false_test, 4,        4,         32,       16,        64,       65536000,   1310720,   5000,         False],
        ["true_test",    true_test,  4,        4,         32,       16,        64,       65536000,   1310720,   96000,        False],
    ]
)

@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        Classifier(test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG, test_params.SAMPLING_FREQUENCY),
        test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG, test_params.SAMPLING_FREQUENCY
    )
    
    msgs = test_params.msgs()
    inputs = [[Fixed(x, True, test_params.BIT_WIDTH, test_params.DECIMAL_PT) for x in sample] for sample in msgs[::2]]
    outputs = [x for x in msgs[1::2]]

    inputs = [fixed_bits(x) for sample in inputs for x in sample]
    outputs = [x for x in outputs]

    th.set_param(
        "top.src.construct",
        msgs=inputs,
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=outputs,
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

    run_sim(th, cmdline_opts, duts=["classifier"])

