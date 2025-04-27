"""
Testbench to test FFT on real data.
Input is a WAV file, the testbench sends the data over SPI and reads the FFT output back.
The testbench is parameterizable by sampling rate (in Hz). If the .wav file is multi-channel,
then it is averaged down to mono before sending it to the FFT.
"""
import wave
import numpy as np
from scipy.signal import resample

# Parse a .wav file to Q8.8 fixed-point format
def wav_to_q8_8_messages(filename: str, target_rate: int) -> bytes:
    # 1)–3) same as before: open, read, channel‑mix, resample…
    with wave.open(filename, "rb") as wf:
        orig_rate = wf.getframerate()
        n_channels = wf.getnchannels()
        sampwidth = wf.getsampwidth()
        n_frames = wf.getnframes()
        # Read all raw bytes for all channels and frames
        raw = wf.readframes(n_frames * n_channels)

    # Process raw bytes based on sample width
    if sampwidth == 3:
        # Handle 24-bit audio (3 bytes)
        raw_bytes = np.frombuffer(raw, dtype=np.uint8)
        if raw_bytes.size % 3 != 0:
            raise ValueError(f"Raw data size {raw_bytes.size} is not divisible by 3 for 24-bit audio.")

        num_samples_total = raw_bytes.size // 3
        reshaped_bytes = raw_bytes.reshape(num_samples_total, 3)

        # Convert 3 bytes (little-endian) to signed int32
        samples_int32 = np.empty(num_samples_total, dtype=np.int32)
        samples_int32[:] = reshaped_bytes[:, 0]  # LSB
        samples_int32 |= (reshaped_bytes[:, 1].astype(np.int32) << 8)
        samples_int32 |= (reshaped_bytes[:, 2].astype(np.int32) << 16) # MSB

        # Sign extend negative values (check MSB of the third byte)
        negative_mask = reshaped_bytes[:, 2] >= 0x80
        # Fill the most significant byte with 1s for negative numbers
        samples_int32[negative_mask] |= np.int32(~0xFFFFFF) # or np.int32(0xFF000000)

        # Assign the processed samples and set dtype for downstream consistency
        samples = samples_int32
        dtype = np.int32
        # Calculate n_frames based on the total samples and channels
        n_frames = num_samples_total // n_channels

    elif sampwidth in [1, 2, 4]:
        # Handle standard sample widths
        dtype_map = {1: np.uint8, 2: np.int16, 4: np.int32}
        dtype = dtype_map[sampwidth]
        # Convert raw bytes to samples using the appropriate dtype
        samples = np.frombuffer(raw, dtype=dtype)
        # Calculate n_frames based on the total samples and channels
        n_frames = len(samples) // n_channels
    else:
        raise ValueError(f"Unsupported sample width: {sampwidth}")

    if n_channels > 1:
        # Reshape requires the total number of samples to be divisible by n_channels
        if samples.size % n_channels != 0:
             raise ValueError(f"Total samples {samples.size} not divisible by number of channels {n_channels}.")
        samples = samples.reshape(-1, n_channels).mean(axis=1).astype(dtype)
    if orig_rate != target_rate:
        new_len = int(len(samples) * target_rate / orig_rate)
        samples = resample(samples, new_len)

    # 4) Normalize to –1..+1
    if np.issubdtype(dtype, np.integer):
        max_val = float(2 ** (8 * sampwidth - 1))
        samples = samples.astype(np.float32) / max_val
    else:
        samples = samples.astype(np.float32)
    samples = np.clip(samples, -1.0, 1.0)

    # 5) Convert to Q8.8 fixed‑point (signed 16‑bit, 8 frac bits)
    #    multiply by 2^8, round, cast to int16
    fixed = np.round(samples * (1 << 8)).astype(np.int16)

    # return raw little‑endian bytes, or list(fixed) for Python ints
    return fixed.tolist()
