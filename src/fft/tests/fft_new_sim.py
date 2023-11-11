import numpy as np
import math
from fixedpt import CFixed
from src.fixed_point.iterative.tests.butterfly import buf

# Implements twiddle generator
def twiddle_gen (bit_width=4, decimal_pt=2, size_fft=8, stage_fft=0):

    twiddles = np.zeros(size_fft)

    for k in range(size_fft):
        angle = -2 * np.pi * k / size_fft
        real_part = CFixed(np.cos(angle), bit_width, decimal_pt)
        imag_part = CFixed(np.sin(angle), bit_width, decimal_pt)

        twiddle = CFixed(0, bit_width, decimal_pt)
        twiddle.value = CFixed(real_part, bit_width, decimal_pt).value + 1j * CFixed(imag_part, bit_width, decimal_pt).value

        twiddles.append(twiddle)

    return twiddles


# Implements one stage of the FFT
def fft_stage(fft_stage_in, stage_fft=0, bit_width=32, decimal_pt=16, n_samples=8):

    buf_in = np.zeros(n_samples)
    buf_out = np.zeros(n_samples)

    # Front crossbar
    for m in range(0, 2**stage_fft):
        for i in range(m, n_samples, 2**(stage_fft+1)):
            buf_in[i+m] = fft_stage_in[i]
            buf_in[i+m+1] = fft_stage_in[i+2**stage_fft]

    # Twiddles (NOT SURE IF IT WORKS)
    twiddles = twiddle_gen(bit_width, decimal_pt, n_samples, stage_fft)

    # Butterflies
    for b in range(0, n_samples/2):
        (buf_out[b*2], buf_out[b*2+1]) = buf(n_samples, decimal_pt, twiddles[b], buf_in[b*2], buf_in[b*2 + 1])

    output = np.zeros(n_samples)

    # Back crossbar
    for m in range(0, 2**stage_fft):
        for i in range(m, n_samples, 2**(stage_fft+1)):
            output[i] = buf_out[i+m]
            output[i+2**stage_fft] = buf_out[i+m+1]

    return output

# Implements fft (DID NOT FINISH)
def fft (fft_in, bit_width=32, decimal_pt=16, n_samples=8):

    # Bit reverse



    # FFT Stages
    stages_out = np.zeros(math.ceil(math.log2(n_samples)))

    for i in range(0, math.ceil(math.log2(n_samples))):
        stages_out[i+1] = fft_stage(fft_in[i], i, bit_width, decimal_pt, n_samples)

    # FFT Out
    fft_out = np.zeros(n_samples)
    for i in range(0, n_samples):
        fft_out[i] = stages_out[math.ceil(math.log2(n_samples))]
    
    

    







