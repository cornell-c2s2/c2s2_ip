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
    print(v)
    print(v * max_fraction_value)
    print(scaled_number)
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

def sine_wave_gen():
    t = np.linspace(0, 1, 16, endpoint=False)  
    freq = 2500  
    A = 100 
    sine_wave = A * np.sin(2 * np.pi * freq * t)
    return sine_wave

def get_fft_mag (arr):
    frq_arr = np.fft.fft(arr)
    mag = np.abs(frq_arr)
    return mag

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, BIT_WIDTH=32, DECIMAL_PT = 16, N_SAMPLES = 8, CUTOFF_FREQ = 65536000, CUTOFF_MAG = 1310720, SAMPLING_FREQUENCY = 44000):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(1))
        s.classifier = ClassifierWrapper(BIT_WIDTH, DECIMAL_PT, N_SAMPLES, CUTOFF_FREQ, CUTOFF_MAG, SAMPLING_FREQUENCY)

        # Connect

        s.src.send //= s.classifier.recv
        s.classifier.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

# -------------------------------------------------------------------------
# Tests
# -------------------------------------------------------------------------
def sine_wave():
    arr = sine_wave_gen()
    frq_arr = np.fft.fft(arr)
    mag = np.abs(frq_arr)
    return [mag, 0]

def below_freq_mag (): # CUTOFF_FREQ = 8250 Hz, CUTOFF_MAG = 10
    return [get_fft_mag([0, 0.27, 0.49, 0.65, 0.7, 0.65, 0.49, 0.27, 0, -0.27, -0.49, -0.65, -0.7, -0.65, -0.49, -0.27]), 0,
            get_fft_mag([0, 0.42, 0.6, 0.42, 0, -0.42, -0.6, -0.42, 0, 0.42, 0.6, 0.42, 0, -0.42, -0.6, -0.42]), 0,
            get_fft_mag([0, 0.4, 0.69, 0.8, 0.69, 0.4, 0, -0.4, -0.69, -0.8, -0.69, -0.4, 0, 0.4, 0.69, 0.8]), 0]

def above_freq_mag (): # CUTOFF_FREQ = 10000 Hz, CUTOFF_MAG = 20
    return [get_fft_mag([20, -20, 20, -20, 20, -20, 20, -20, 20, -20, 20, -20, 20, -20, 20, -20]), 1,
            get_fft_mag([ 0.00000000e+00,  2.44929360e-15, -4.89858720e-15,  7.34788079e-15,
                         -9.79717439e-15,  1.22464680e-14, -1.46957616e-14,  1.71450552e-14,
                         -1.95943488e-14,  2.20436424e-14, -2.44929360e-14,  9.79965032e-14,
                         -2.93915232e-14, -3.92134568e-14, -3.42901104e-14,  1.07793678e-13]), 1,
            get_fft_mag([ -5.01839525,  18.02857226,   9.27975767,   3.94633937, -13.75925438,
                         -13.76021919, -17.67665551,  14.64704583,   4.04460047,   8.32290311,
                         -19.17662023,  18.79639409,  13.29770563, -11.50643557, -12.72700131,
                         -12.66381961]), 1]

def above_freq_below_mag (): # CUTOFF_FREQ = 10000 Hz, CUTOFF_MAG = 20
    return [get_fft_mag([2.0,
                        2.914213562373095,
                        3.0616169978683826e-16,
                        -2.914213562373095,
                        -2.0000000000000004,
                        0.08578643762690463,
                        1.8369701987210302e-16,
                        -0.0857864376269053,
                        1.9999999999999993,
                        2.9142135623730954,
                        1.5308084989341917e-15,
                        -2.914213562373093,
                        -2.000000000000001,
                        0.08578643762690574,
                        4.286263797015736e-16,
                        -0.08578643762690685]), 0,
            get_fft_mag([ 0.0,
                            1.8477590650225735,
                            -1.414213562373095,
                            -0.7653668647301808,
                            2.0,
                            -0.7653668647301797,
                            -1.414213562373097,
                            1.8477590650225728,
                            1.2246467991473533e-15,
                            -1.8477590650225737,
                            1.4142135623730951,
                            0.7653668647301787,
                            -2.0,
                            0.7653668647301752,
                            1.4142135623730978,
                            -1.8477590650225724]), 0,
            get_fft_mag([ -0.6400509785799624,
                            -4.740737681721087,
                            0.49662477878709144,
                            -0.6467760738172315,
                            -0.7963219791251097,
                            -1.6966517899612588,
                            -2.953513659621575,
                            1.192709663506637,
                            -2.0034532632547686,
                            -2.3317272489713337,
                            1.2113383276929488,
                            0.2914209427703902,
                            -3.6542005465506646,
                            0.13578121265746468,
                            -3.155601343530847,
                            2.8533514781667346]), 0]

def one_true (): # CUTOFF_FREQ = 10000 Hz, CUTOFF_MAG = 40
    return [get_fft_mag([40, -40, 40, -40, 40, -40, 40, -40, 40, -40, 40, -40, 40, -40, 40, -40]), 1,
            get_fft_mag([40 * np.sin(2 * np.pi * 4 * t / 16) for t in np.arange(16) ]), 1,
            get_fft_mag([ 20 * np.sin(2 * np.pi * 3 * t / 16) + 20 * np.cos(2 * np.pi * 5 * t / 16) for t in np.arange(16) ]), 1]


test_case_table = mk_test_case_table(
    [
        (
                                  "msgs                  src_delay sink_delay BIT_WIDTH DECIMAL_PT N_SAMPLES CUTOFF_FREQ CUTOFF_MAG SAMPLING_FREQUENCY slow"
        ),
        #["below_freq_mag",         below_freq_mag,       4,        4,         32,       16,        16,       540672000,   655360,     44000,         False],
        ["above_freq_mag",         above_freq_mag,       4,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        #["above_freq_below_mag",   above_freq_below_mag, 4,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        #["one_true",               one_true,             4,        4,         32,       16,        16,       655360000,   2621440,    44000,         False],



        #["b_freq_l_amp_sin_1",   b_freq_l_amp_sin_1, 4,        4,         32,       16,        16,       32768000,   32768,     44000,         False],
        #["b_freq_l_amp_sin_2",   b_freq_l_amp_sin_2, 4,        4,         32,       16,        16,       32768000,   32768,     44000,         False],
        # ["sine_wave",   sine_wave, 4,        4,         32,       16,        16,       32768000,   32768,     44000,         False],
        # ["false_test",   false_test, 4,        4,         32,       16,        16,       65536000,   1310720,   50000,         False],
        # ["true_test",    true_test,                  4,        4,         32,       10,        16,       65536000,   1310720,   96000,        False],
    ]
)

@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG, test_params.SAMPLING_FREQUENCY)
    
    # msgs = test_params.msgs()
    # inputs = [[Fixed(x, True, test_params.BIT_WIDTH, test_params.DECIMAL_PT) for x in sample] for sample in msgs[::2]]
    # outputs = [x for x in msgs[1::2]]

    # inputs = [fixed_bits(x) for sample in inputs for x in sample]
    # outputs = [x for x in outputs]
    msgs = test_params.msgs()
    print(msgs)
    #msgs = [make_arr_fixed(test_params.BIT_WIDTH, test_params.DECIMAL_PT, x) if i%2 != 0 else x for i, x in enumerate(msgs, start=1)]
    # msgs = [mk_packed(test_params.BIT_WIDTH)(*x) if i%2 != 0 else x for i, x in enumerate(msgs, start=1)]

    inputs = [make_fixed(test_params.BIT_WIDTH, test_params.DECIMAL_PT, x) for sample in msgs[::2] for x in sample]
    print("now inputs")
    print(inputs)
    print("now ouputs")
    outputs = [x for x in msgs[1::2]]
    print(outputs)

    th.set_param(
        "top.src.construct",
        msgs=inputs[::2],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=outputs[1::2],
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

    run_sim(th, cmdline_opts, duts=["classifier"])

