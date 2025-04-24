import pyaudio
import numpy as np
import time
import matplotlib.pyplot as plt

import wave

# Audio config
SAMPLE_RATE = 3200
CHUNK_DURATION = 1.0 / SAMPLE_RATE  # seconds
RATE = 44100  # samples per second
CHUNK_SIZE = int(RATE * CHUNK_DURATION)  # samples per chunk
FORMAT = pyaudio.paInt16
CHANNELS = 1

# Start PyAudio
p = pyaudio.PyAudio()
audio_bytes = []
audio_vals = np.array([]).astype(np.int16)

# Open stream for microphone input
stream = p.open(format=FORMAT,
                channels=CHANNELS,
                rate=RATE,
                input=True,
                frames_per_buffer=CHUNK_SIZE)

print("Sampling audio at 32 kHz... Press Ctrl+C to stop.")
try:
    while True:
        # Read audio chunk
        data = stream.read(CHUNK_SIZE, exception_on_overflow=False)
        audio_bytes.append(data)  # Save raw audio data
       
        # Convert bytes to numpy array
        sample = np.frombuffer(data, dtype=np.int16)
        audio_vals = np.concatenate((audio_vals, sample))


except KeyboardInterrupt:
    print("Stopping.")


finally:
    stream.stop_stream()
    stream.close()
    p.terminate()

    # print(audio_bytes)
    print(audio_vals)

    # Save recorded audio to a .wav file
    output_filename = "recorded_audio.wav"
    wf = wave.open(output_filename, 'wb')
    wf.setnchannels(CHANNELS)
    wf.setsampwidth(p.get_sample_size(FORMAT))
    wf.setframerate(RATE)
    wf.writeframes(b''.join(audio_bytes))
    wf.close()

    print(f"Audio saved to '{output_filename}'")
   
    # X = np.fft.fft(audio_vals)
    # N = len(X)
    # n = np.arange(N)
    # T = N/sr
    # freq = n/T
    # plt.plot(audio_vals)
    # plt.show()
    # # plt.plot(np.fft.fft(audio_vals))
    # plt.stem(freq, np.abs(X), 'b', \
    #      markerfmt=" ", basefmt="-b")
    # plt.show()