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
# from src.classifier.classifier import ClassifierWrapper
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

def get_fft_real (arr):
    fft_arr = np.fft.fft(arr)
    real = np.real(fft_arr)
    return real

def classifier(fft_arr, cutoff_frq, cutoff_mag):
    fft_mags = np.abs(np.real(fft_arr))
    frq_arr = np.fft.fftfreq(len(fft_arr), 1/44000)
    fft_hi_pass = fft_mags[np.nonzero(frq_arr>cutoff_frq)]
    max_amplitude = np.max(fft_hi_pass)
    
    if max_amplitude > cutoff_mag:
        return 1
    else: 
        return 0

def generate_sine_wave_below_mag(frequency, sample_freq, cutoff_mag):
    length = 16
    t = np.arange(0, length * (1/sample_freq), (1/sample_freq))
    amplitude = cutoff_mag / 100
    sine_wave = amplitude * np.sin(2 * np.pi * frequency * t)
    
    fft_output = np.fft.fft(sine_wave)
    real_part = np.abs(fft_output.real)

    if np.any(real_part > cutoff_mag):
        print("Adjusting amplitude to meet requirements...")
        sine_wave *= (cutoff_mag / np.max(real_part))
    
    return sine_wave


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

# -------------------------------------------------------------------------
# Tests
# -------------------------------------------------------------------------
def below_freq_mag (): # CUTOFF_FREQ = 8250 Hz, CUTOFF_MAG = 10
    input_1 = [0, 0.27, 0.49, 0.65, 0.7, 0.65, 0.49, 0.27, 0, -0.27, -0.49, -0.65, -0.7, -0.65, -0.49, -0.27]
    input_2 = [0, 0.42, 0.6, 0.42, 0, -0.42, -0.6, -0.42, 0, 0.42, 0.6, 0.42, 0, -0.42, -0.6, -0.42]
    input_3 = [0, 0.4, 0.69, 0.8, 0.69, 0.4, 0, -0.4, -0.69, -0.8, -0.69, -0.4, 0, 0.4, 0.69, 0.8]
    return [get_fft_real(input_1), classifier(np.fft.fft(input_1), 8250, 10),
            get_fft_real(input_2), classifier(np.fft.fft(input_2), 8250, 10),
            get_fft_real(input_3), classifier(np.fft.fft(input_3), 8250, 10)]

def above_freq_mag (): # CUTOFF_FREQ = 10000 Hz, CUTOFF_MAG = 20
    input_1 = [ 1.00000000e+01,  2.83276945e-15, -1.00000000e+01, -1.83697020e-15,
          1.00000000e+01,  1.19434012e-14, -1.00000000e+01, -4.28626380e-15,
          1.00000000e+01,  2.32744790e-14, -1.00000000e+01, -2.44991258e-14,
          1.00000000e+01,  2.57237726e-14, -1.00000000e+01, -2.69484194e-14]
    input_2 = [ 1.00000000e+01, -3.82683432e+00, -7.07106781e+00,  9.23879533e+00,
          1.19434012e-14, -9.23879533e+00,  7.07106781e+00,  3.82683432e+00,
         -1.00000000e+01,  3.82683432e+00,  7.07106781e+00, -9.23879533e+00,
          8.57871740e-15,  9.23879533e+00, -7.07106781e+00, -3.82683432e+00]
    input_3 = [ 1.00000000e+01, -7.07106781e+00, -1.83697020e-15,  7.07106781e+00,
         -1.00000000e+01,  7.07106781e+00, -1.22526578e-14, -7.07106781e+00,
          1.00000000e+01, -7.07106781e+00,  8.57871740e-15,  7.07106781e+00,
         -1.00000000e+01,  7.07106781e+00, -4.90477700e-15, -7.07106781e+00]
    return [get_fft_real(input_1), classifier(np.fft.fft(input_1), 10000, 20),
            get_fft_real(input_2), classifier(np.fft.fft(input_2), 10000, 20),
            get_fft_real(input_3), classifier(np.fft.fft(input_3), 10000, 20)]

def above_freq_below_mag (): # CUTOFF_FREQ = 10000 Hz, CUTOFF_MAG = 20
    input_1 = [ 2.0,
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
                -0.08578643762690685]
    input_2 = [ 0.0,
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
                -1.8477590650225724]
    input_3 = [ -0.6400509785799624,
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
                2.8533514781667346]
    return [get_fft_real(input_1), classifier(np.fft.fft(input_1), 10000, 20),
            get_fft_real(input_2), classifier(np.fft.fft(input_2), 10000, 20),
            get_fft_real(input_3), classifier(np.fft.fft(input_3), 10000, 20)]

def one_true (): # CUTOFF_FREQ = 10000 Hz, CUTOFF_MAG = 40
    input_1 = [40, -40, 40, -40, 40, -40, 40, -40, 40, -40, 40, -40, 40, -40, 40, -40]
    input_2 = [40 * np.sin(2 * np.pi * 4 * t / 16) for t in np.arange(16) ]
    input_3 = [ 20 * np.sin(2 * np.pi * 3 * t / 16) + 20 * np.cos(2 * np.pi * 5 * t / 16) for t in np.arange(16) ]
    return [get_fft_real(input_1), classifier(np.fft.fft(input_1), 10000, 40),
            get_fft_real(input_2), classifier(np.fft.fft(input_2), 10000, 40),
            get_fft_real(input_3), classifier(np.fft.fft(input_3), 10000, 40)]

def random_4_decimal (): # BIT_WIDTH = 32, DECIMAL_PT = 4
    np.random.seed(42)
    length = 16
    random_1 = [random.uniform(0, 25000000) for _ in range(length)]
    random_2 = [random.uniform(0, 25000000) for _ in range(length)]
    random_3 = [random.uniform(0, 25000000) for _ in range(length)]
    random_4 = [random.uniform(0, 25000000) for _ in range(length)]
    return [get_fft_real(random_1), classifier(np.fft.fft(random_1), 10000, 200),
            get_fft_real(random_2), classifier(np.fft.fft(random_2), 10000, 200),
            get_fft_real(random_3), classifier(np.fft.fft(random_3), 10000, 200),
            get_fft_real(random_4), classifier(np.fft.fft(random_4), 10000, 200)]

def random_8_decimal (): # BIT_WIDTH = 32, DECIMAL_PT = 8
    np.random.seed(42)
    length = 16
    random_1 = [random.uniform(0, 250000) for _ in range(length)]
    random_2 = [random.uniform(0, 250000) for _ in range(length)]
    random_3 = [random.uniform(0, 250000) for _ in range(length)]
    random_4 = [random.uniform(0, 250000) for _ in range(length)]
    return [get_fft_real(random_1), classifier(np.fft.fft(random_1), 10000, 200),
            get_fft_real(random_2), classifier(np.fft.fft(random_2), 10000, 200),
            get_fft_real(random_3), classifier(np.fft.fft(random_3), 10000, 200),
            get_fft_real(random_4), classifier(np.fft.fft(random_4), 10000, 200)]

def random_16_decimal (): # BIT_WIDTH = 32, DECIMAL_PT = 16
    np.random.seed(42)
    length = 16
    random_1 = [random.uniform(0, 2500) for _ in range(length)]
    random_2 = [random.uniform(0, 2500) for _ in range(length)]
    random_3 = [random.uniform(0, 2500) for _ in range(length)]
    random_4 = [random.uniform(0, 2500) for _ in range(length)]
    return [get_fft_real(random_1), classifier(np.fft.fft(random_1), 10000, 200),
            get_fft_real(random_2), classifier(np.fft.fft(random_2), 10000, 200),
            get_fft_real(random_3), classifier(np.fft.fft(random_3), 10000, 200),
            get_fft_real(random_4), classifier(np.fft.fft(random_4), 10000, 200)]

def sine_wave_below_mag():
    cutoff_mag = 20
    sample_freq = 44000
    frequencies = [100, 500, 1000, 5000]
    sine_wave = [generate_sine_wave_below_mag(f, sample_freq, cutoff_mag) for f in frequencies]
    return [get_fft_real(sine_wave[0]), classifier(np.fft.fft(sine_wave[0]), 10000, 200),
            get_fft_real(sine_wave[1]), classifier(np.fft.fft(sine_wave[1]), 10000, 200),
            get_fft_real(sine_wave[2]), classifier(np.fft.fft(sine_wave[2]), 10000, 200),
            get_fft_real(sine_wave[3]), classifier(np.fft.fft(sine_wave[3]), 10000, 200)]

# def random_sines():
#     np.random.seed(42)
#     length = 16
#     sample_freq = 44000
#     t = np.arange(0, length * (1/sample_freq), (1/sample_freq))
#     rand_frequencies = [np.random.uniform(0, 20000) for _ in range(8)]
#     rand_amplitudes = [np.random.uniform(0, 2000) for _ in range(8)]
#     sine_wave = [a*np.sin(2 * np.pi * f * t) for a in rand_amplitudes for f in rand_frequencies]
#     returning = []
#     for i in range(64):
#         returning.append(get_fft_real(sine_wave[i]))
#         returning.append(classifier(np.fft.fft(sine_wave[i]), 10000, 200))
#     return returning


test_case_table = mk_test_case_table(
    [
        (
                                  "msgs                  src_delay sink_delay BIT_WIDTH DECIMAL_PT N_SAMPLES CUTOFF_FREQ CUTOFF_MAG SAMPLING_FREQUENCY slow"
        ),
        ["below_freq_mag",         below_freq_mag,       4,        4,         32,       16,        16,       540672000,   655360,     44000,         False],
        ["above_freq_mag",         above_freq_mag,       4,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        ["above_freq_below_mag",   above_freq_below_mag, 4,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        ["random_4_decimal",       random_4_decimal,     4,        4,         32,       4 ,        16,       160000   ,   320    ,    44000,         False],
        ["random_8_decimal",       random_8_decimal,     4,        4,         32,       8 ,        16,       2560000  ,   5120   ,    44000,         False],
        ["random_16_decimal",      random_16_decimal,    4,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        ["sine_wave_below_mag",    sine_wave_below_mag,  4,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        ["input_delay_small",      above_freq_mag,       1,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        ["input_delay_big",        above_freq_mag,       8,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
        ["output_delay_small",     above_freq_mag,       4,        1,         32,       16,        16,       655360000,   1310720,    44000,         False],
        ["output_delay_small",     above_freq_mag,       4,        8,         32,       16,        16,       655360000,   1310720,    44000,         False],
        #["random_sines",           random_sines,         4,        4,         32,       16,        16,       655360000,   1310720,    44000,         False],
    ]
)

@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        Classifier(test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG, test_params.SAMPLING_FREQUENCY),
        test_params.BIT_WIDTH, test_params.DECIMAL_PT, test_params.N_SAMPLES, test_params.CUTOFF_FREQ, test_params.CUTOFF_MAG, test_params.SAMPLING_FREQUENCY
    )
    
    # msgs = test_params.msgs()
    # inputs = [[Fixed(x, True, test_params.BIT_WIDTH, test_params.DECIMAL_PT) for x in sample] for sample in msgs[::2]]
    # outputs = [x for x in msgs[1::2]]

    # inputs = [fixed_bits(x) for sample in inputs for x in sample]
    # outputs = [x for x in outputs]
    msgs = test_params.msgs()
    msgs = [make_arr_fixed(test_params.BIT_WIDTH, test_params.DECIMAL_PT, x) if i%2 != 0 else x for i, x in enumerate(msgs, start=1)]
    msgs = [mk_packed(test_params.BIT_WIDTH)(*x) if i%2 != 0 else x for i, x in enumerate(msgs, start=1)]

    print(msgs[1::2])

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

