
import pdb

# Inputs:
# cutoff_freq: Classifier cutoff freq (unsigned int)
# cutoff_mag: Classifier cutoff magnitude (unsigned int)
# sampling_freq: Sampling freq of audio data
# recv_msg: Input bins from FFT
# parameters: An array of classifier parameter values (Set to default params by default)
# [BIT_WIDTH, DECIMAL_BIT, FREQ_BIT_WIDTH, N_SAMPLES]

def classify (cutoff_freq, cutoff_mag, sampling_freq, recv_msg, parameters=[32,16,8,8]):
    # Extract parameters (half of them aren't used, thanks tomas...)
    BIT_WIDTH = parameters[0]
    DECIMAL_BIT = parameters[1]
    FREQ_BIT_WIDTH = parameters[2]
    N_SAMPLES = parameters[3]

    cutoff_mag = cutoff_mag / 2**(DECIMAL_BIT) # Convert to fixed point

    bin_resolution = sampling_freq/(N_SAMPLES*2)

    # Compute magnitude
    out_mag = [0] * N_SAMPLES      # Magnitudes of each bin
    bin_freqs = [0] * N_SAMPLES    # Tracks bin freqs
    freq_val = [0] * N_SAMPLES     # Tracks bins w/ valid freq (1 val, 0 otherwise)
    mag_val = [0] * N_SAMPLES      # Tracks bins w/ valid mag
    bins_val = [0] * N_SAMPLES     # Tracks bins w/ valid mag and freq

    send_msg = 0

    for idx,bin in enumerate(recv_msg):
        # Compute bin magnitude
        out_mag[idx] = abs(bin)
        bin_freqs[idx] += bin_resolution*idx
        
        # Compute frequency range in each bin
        if(bin_freqs[idx] >= cutoff_freq):
            freq_val[idx] = 1
        else:
            freq_val[idx] = 0

        # Compute bins with frequencies greater than cutoff
        if(bin_freqs[idx] >= cutoff_freq):
            freq_val[idx] = 1
        else:
            freq_val[idx] = 0

        # Compute bins with magnitude greater than cutoff
        if(out_mag[idx] >= cutoff_mag):
            mag_val[idx] = 1
        else:
            mag_val[idx] = 0

        # Compute bins with valid mag and freq
        if(mag_val[idx] and freq_val[idx]):
            bins_val[idx] = 1
            send_msg = 1
        else:
            bins_val[idx] = 0
    # pdb.set_trace()
    return [send_msg, freq_val, mag_val, bins_val]

