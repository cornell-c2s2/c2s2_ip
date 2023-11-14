#!/usr/bin/env python

import numpy as np
import math
import random
from fixedpt import CFixed
from src.fixed_point.iterative.tests.butterfly import butterfly

# Implements twiddle generator
def twiddle_gen (bit_width=4, decimal_pt=2, size_fft=8, stage_fft=0):

    twiddles = [] * (size_fft//2)

    for m in range(0, 2 ** stage_fft):
        for i in range(0, size_fft, 2 ** (stage_fft + 1)):
            idx = m * size_fft / (1 << (stage_fft + 1))
            
            real = CFixed(np.sin((idx+size_fft/4)%size_fft), bit_width, decimal_pt)
            imag = CFixed(-np.sin(idx%size_fft), bit_width, decimal_pt)

            twiddle = CFixed(0, bit_width, decimal_pt)
            twiddle.value = CFixed(real, bit_width, decimal_pt).value + 1j * CFixed(imag, bit_width, decimal_pt).value

            twiddles[i/2+m] = twiddle

    return twiddles


# Implements bit reverse
def bit_reverse (input, bit_width=32, n_samples=8):

    out = [0] * n_samples 
    n = math.ceil(math.log2(n_samples))

    for m in range(0, n_samples):
        m_rev = [] * math.ceil(math.log2(n_samples))
        for i in range(0, n):
            m_rev[n-i-1] = m[i]
        out[m_rev] = input[m]
    
    return out


# Implements one stage of the FFT
def fft_stage(fft_stage_in, stage_fft=0, bit_width=32, decimal_pt=16, n_samples=8):

    print('stage_fft', stage_fft)
    print('bit_width', bit_width)
    print('decimal_pt', decimal_pt)
    print('n_samples', n_samples)
    
    buf_in = [0] * n_samples
    buf_out = [0] * n_samples

    # Front crossbar
    for m in range(0, 2**stage_fft):
        for i in range(m, n_samples, 2**(stage_fft+1)):
            print('i+m', i+m)
            print('i+m+1', i+m+1)
            buf_in[i+m] = fft_stage_in[i]
            buf_in[i+m+1] = fft_stage_in[i+2**stage_fft]

    # Twiddles 
    twiddles = twiddle_gen(bit_width, decimal_pt, n_samples, stage_fft)

    # Butterflies
    for b in range(0, n_samples/2):
        (buf_out[b*2], buf_out[b*2+1]) = butterfly(n_samples, decimal_pt, twiddles[b], buf_in[b*2], buf_in[b*2 + 1])

    output = [] * n_samples

    # Back crossbar
    for m in range(0, 2**stage_fft):
        for i in range(m, n_samples, 2**(stage_fft+1)):
            output[i] = buf_out[i+m]
            output[i+2**stage_fft] = buf_out[i+m+1]

    return output

# Implements fft 
def fft (fft_in, bit_width=32, decimal_pt=16, n_samples=8):

    # Bit reverse
    stages_out = bit_reverse(fft_in, bit_width, n_samples)

    # FFT Stages
    stages_out = [0] * n_samples

    for i in range(0, math.ceil(math.log2(n_samples))):
        stages_out[i+1] = fft_stage(fft_in[i], i, bit_width, decimal_pt, n_samples)

    # FFT Out
    fft_out = [] * n_samples
    for i in range(0, n_samples):
        fft_out[i] = stages_out[math.ceil(math.log2(n_samples))]
    
    return stages_out

# return a random fixed point value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )

def main():

    rand_cfxp = [rand_cfixed(32, 16) for i in range(8)]
    print(rand_cfxp)
    
    fft_stage_output = fft_stage(rand_cfxp, 0, 32, 16, 8)

    print(fft_stage_output)


if __name__ == "__main__":
    main()
