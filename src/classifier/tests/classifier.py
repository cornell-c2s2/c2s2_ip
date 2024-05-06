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
# from src.fft.demos.classifier import classify

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

def generate_sine_wave_below_mag(frequency, sample_freq, cutoff_mag):
    length = 16
    t = np.arange(0, length * (1/sample_freq), (1/sample_freq))
    amplitude = cutoff_mag / 100
    sine_wave = amplitude * np.sin(2 * np.pi * frequency * t)
    
    fft_output = np.fft.fft(sine_wave)
    real_part = np.abs(fft_output.real)

    if np.any(real_part > cutoff_mag):
        sine_wave *= (cutoff_mag / np.max(real_part))
    
    return sine_wave

def classify(magnitudes: list[list[float]], bins: list[float]) -> list[bool]:
    # Cutoff values for frequency
    low = 2700
    high = 9000

    # Magnitude threshold
    threshold = 0.01

    count = 0
    classifications = []

    on_cycle = 0 # Consecutive cycles with magnitude above threshold
    off_cycle = 0 # Consecutive cycles with magnitude below threshold

    curr_sound = False # Whether or not we are on a sound

    convVert = 0
    convUpHalf = 0
    convLowHalf = 0

    for j, sample in enumerate(magnitudes):
        
        counter = 0

        max_mag = 0

        # Check if there is a bin with a magnitude above the threshold
        for i, mag in enumerate(sample):
            # Vertical convolution
            if (bins[i] > low):
                convVert += mag
            
            # Convolution for Upper Half (between 11350 - 20000)
            if (bins[i] > 11350 and bins[i] < 20000): # consider dividing into thirds, multiplying middle by 2 and rest by 1
                convUpHalf += mag * 2
                convLowHalf -= mag * 2
                
            # Convolution for Lower Half (between 2700 - 11350)
            if (bins[i] > 2700 and bins[i] < 11350): 
                convLowHalf += mag * 2
                convUpHalf -= mag * 2

            if mag > threshold:
                if bins[i] < low or bins[i] > high:
                    if (mag > max_mag):
                        max_mag = mag * 0.1
                    # Reduce magnitude outside the interval
                else:
                    if (mag * 20 > max_mag):
                        max_mag = mag * 20
                        
                    # Amplify magnitude within the interval
                    
                counter += 1
        if (counter == 0):
            classifications.append([0] * 7)
            continue
        if (max_mag > 0.5):
            on_cycle += 1
            off_cycle = 0

        elif (max_mag < 0.3):
            if (curr_sound == False): # Resetting Convolutions
                convVert = 0
                convUpHalf = 0
                convLowHalf = 0
            on_cycle = 0
            off_cycle += 1
        
        # When there are 300 cycles with a magnitude > 0.5, then curr_sound is true indicating we are on a sound
        if (on_cycle > 300):
            curr_sound = True
        
        # When 2000 cycles pass with magnitude < 0.3, then we get out of any sound we may be in
        elif (off_cycle > 2000):
            curr_sound = False
        
        if (curr_sound == True):
            if (convLowHalf > convVert):
                count = 10
        else:
            count = 0
        if (count > 0):
            count -= 1

        # classifications.append([max_mag, convVert, convUpHalf, convLowHalf, math.log2(max_mag), count, on_cycle])
        classifications.append(count)

    return classifications

# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, classifier, BIT_WIDTH=32, N_SAMPLES = 8):
        # Instantiate models
        
        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH*N_SAMPLES))
        s.cutoff_idx_low = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.cutoff_idx_high = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.cutoff_mag = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(1))
        s.classifier = classifier

        # Connect

        s.cutoff_idx_low.send //= s.classifier.cutoff_idx_low
        s.cutoff_idx_high.send //= s.classifier.cutoff_idx_high
        s.cutoff_mag.send //= s.classifier.cutoff_mag
        s.src.send //= s.classifier.recv
        s.classifier.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

# -------------------------------------------------------------------------
# Tests
# -------------------------------------------------------------------------

def basic_test ():

    input_1 = [0, 0.27, 0.49, 0.65, 0.7, 0.65, 0.49, 0.27, 0, -0.27, -0.49, -0.65, -0.7, -0.65, -0.49, -0.27]
    input_2 = [0, 0.42, 0.6, 0.42, 0, -0.42, -0.6, -0.42, 0, 0.42, 0.6, 0.42, 0, -0.42, -0.6, -0.42]
    input_3 = [0, 0.4, 0.69, 0.8, 0.69, 0.4, 0, -0.4, -0.69, -0.8, -0.69, -0.4, 0, 0.4, 0.69, 0.8]

    fft_real_1 = np.fft.fft(input_1).real
    fft_real_2 = np.fft.fft(input_2).real
    fft_real_3 = np.fft.fft(input_3).real

    n_samples = 16
    sample_rate = 44000

    bins = np.fft.fftfreq(n_samples, 1 / sample_rate)[: n_samples // 2]

    cutoff_idx_low = 5
    cutoff_idx_high = 10

    return [cutoff_idx_low, cutoff_idx_high, 0.01,
            get_fft_real(input_1), classify(fft_real_1, bins),
            get_fft_real(input_2), classify(fft_real_2, bins),
            get_fft_real(input_3), classify(fft_real_3, bins)]


test_case_table = mk_test_case_table(
    [
        (
                                  "msgs                  src_delay sink_delay BIT_WIDTH N_SAMPLES slow"
        ),
        ["basic_test",             basic_test,           4,        4,         32,       16,       False]
    ]
)

@pytest.mark.parametrize(**test_case_table)
def test(test_params, cmdline_opts):
    th = TestHarness(
        Classifier(test_params.BIT_WIDTH, test_params.N_SAMPLES),
        test_params.BIT_WIDTH, test_params.N_SAMPLES
    )

    msgs = test_params.msgs()

    print(msgs)

    input_data = msgs[3::2]

    print(input_data)

    input_data = [mk_packed(test_params.BIT_WIDTH)(*x) for x in input_data]

    print(input_data)

    cutoff_idx_low = msgs[0]

    print(cutoff_idx_low)

    cutoff_idx_high = msgs[1]

    print(cutoff_idx_high)

    cutoff_mag = msgs[2]

    print(cutoff_mag)

    output_data = msgs[4::2]

    print(output_data)

    th.set_param(
        "top.src.construct",
        msgs=input_data,
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.cutoff_idx_low.construct",
        msgs=[cutoff_idx_low,cutoff_idx_low,cutoff_idx_low],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.cutoff_idx_high.construct",
        msgs=[cutoff_idx_high,cutoff_idx_high,cutoff_idx_high],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.cutoff_mag.construct",
        msgs=[cutoff_mag,cutoff_mag,cutoff_mag],
        initial_delay=test_params.src_delay,
        interval_delay=test_params.src_delay,
    )

    th.set_param(
        "top.sink.construct",
        msgs=output_data,
        initial_delay=test_params.sink_delay,
        interval_delay=test_params.sink_delay,
    )

    run_sim(th, cmdline_opts, duts=["classifier"])

