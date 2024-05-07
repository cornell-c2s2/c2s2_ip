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
from fixedpt import CFixed, Fixed
import wave
from src.serdes.deserializer import Deserializer
from src.serdes.serializer import Serializer
from tools.utils import fixed_bits, mk_test_matrices
from src.fft.demos.classifier import classify, run_spectrogram


# -------------------------------------------------------------------------
# Classifier Wrapper
# -------------------------------------------------------------------------
class ClassifierWrapper(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=32, N_SAMPLES=8):

        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.cutoff_idx_low = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.cutoff_idx_high = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.cutoff_mag = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(1))

        # Hook up configs
        s.cutoff_idx_low.msg //= s.dut.cutoff_idx_low_msg
        s.cutoff_idx_low.val //= s.dut.cutoff_idx_low_val
        s.dut.cutoff_idx_low_rdy //= s.cutoff_idx_low.rdy

        s.cutoff_idx_high.msg //= s.dut.cutoff_idx_high_msg
        s.cutoff_idx_high.val //= s.dut.cutoff_idx_high_val
        s.dut.cutoff_idx_high_rdy //= s.cutoff_idx_high.rdy

        s.cutoff_mag.msg //= s.dut.cutoff_mag_msg
        s.cutoff_mag.val //= s.dut.cutoff_mag_val
        s.dut.cutoff_mag_rdy //= s.cutoff_mag.rdy

        # Hook up a deserializer
        s.deserializer = Deserializer(BIT_WIDTH, N_SAMPLES)
        s.recv.msg //= s.deserializer.recv_msg
        s.recv.val //= s.deserializer.recv_val
        s.deserializer.recv_rdy //= s.recv.rdy

        s.dut = Classifier

        # Hook up the deserializer to the FFT
        for i in range(N_SAMPLES):
            s.deserializer.send_msg[i] //= s.dut.recv_msg[i]

        s.deserializer.send_val //= s.dut.recv_val
        s.dut.recv_rdy //= s.deserializer.send_rdy

        # Output
        s.dut.send_msg //= s.recv.msg
        s.dut.send_val //= s.recv.val
        s.recv.rdy //= s.dut.send_rdy

    def line_trace(s):
        return f"{s.deserializer.line_trace()} > {s.dut.line_trace()}"


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, BIT_WIDTH=32, N_SAMPLES=8):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.cutoff_idx_low = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.cutoff_idx_high = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.cutoff_mag = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(1))
        s.dut = ClassifierWrapper(BIT_WIDTH, N_SAMPLES)

        # Connect

        s.cutoff_idx_low.send //= s.dut.cutoff_idx_low
        s.cutoff_idx_high.send //= s.dut.cutoff_idx_high
        s.cutoff_mag.send //= s.dut.cutoff_mag
        s.src.send //= s.dut.recv
        s.dut.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()


# ----------------------------------------------------------------------
# Helper Functions
# ----------------------------------------------------------------------


# -------------------------------------------------------------------------
# Tests
# -------------------------------------------------------------------------


def check_classifier(
    bit_width: int,
    n_samples: int,
    cmdline_opts: dict,
    src_delay: int,
    sink_delay: int,
    config_delay: int,
    inputs: list[list[Fixed]],
    cutoff_idx_low: int,
    cutoff_idx_high: int,
    cutoff_mag: Fixed,
    outputs: list[bool],
) -> None:
    """
    Check the Classifier implementation.

    Args:
        bit_width (int): Number of bits.
        n_samples (int): Number of samples.
        cmdline_opts (dict): Command line options.
        src_delay (int): Source delay.
        sink_delay (int): Sink delay.
        config_delay (int): Configuration/parameter delay.
        inputs (list[list[Fixed]]): List of inputs (only contains the real part of the complex fft output).
        outputs (list[bool]): List of expected outputs (on or off).

    Returns:
        bool: True if the test passes, False otherwise.
    """
    assert all(len(x) == n_samples for x in inputs)

    model = TestHarness(bit_width, n_samples)

    # Convert inputs and outputs into a single list of bits
    inputs = [fixed_bits(x) for sample in inputs for x in sample]
    outputs = outputs

    # Run the model
    model.set_param(
        "top.src.construct",
        msgs=inputs,
        initial_delay=src_delay + 3,
        interval_delay=src_delay,
    )

    model.set_param(
        "top.cutoff_idx_low.construct",
        msgs=cutoff_idx_low,
        initial_delay=config_delay,
        interval_delay=config_delay,
    )

    model.set_param(
        "top.cutoff_idx_high.construct",
        msgs=cutoff_idx_high,
        initial_delay=config_delay,
        interval_delay=config_delay,
    )

    model.set_param(
        "top.cutoff_mag.construct",
        msgs=cutoff_mag,
        initial_delay=config_delay,
        interval_delay=config_delay,
    )

    model.set_param(
        "top.sink.construct",
        msgs=outputs,
        initial_delay=sink_delay + 3,
        interval_delay=sink_delay,
    )

    run_sim(model, cmdline_opts, duts=["dut"], print_line_trace=False)


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16), (16, 8)],
            "n_samples": [8, 16, 32, 64],
            "slow": True,
        }
    )
)
def test_audio(cmdline_opts, p):

    sample_rate = 44800

    audio_file = "SSR4F_MixPre-1390_01.WAV"

    # TODO: Configure this later
    cutoff_idx_low = 5
    cutoff_idx_high = 10
    cutoff_mag = Fixed(0.01, 1, p.fp_spec[0], p.fp_spec[1])

    # Generate random inputs
    inputs, outputs = run_spectrogram(
        sample_rate, audio_file, cutoff_idx_low, cutoff_idx_high, cutoff_mag
    )
    inputs = [
        [Fixed(x, 1, p.fp_spec[0], p.fp_spec[1]) for x in sample] for sample in inputs
    ]

    print("Generated Data")

    check_classifier(
        p.fp_spec[0],
        p.n_samples,
        cmdline_opts,
        src_delay=3,
        sink_delay=3,
        config_delay=1,
        inputs=inputs,
        cutoff_idx_low=cutoff_idx_low,
        cutoff_idx_high=cutoff_idx_high,
        cutoff_mag=cutoff_mag,
        outputs=outputs,
    )
