import pytest
import random
import math
from pymtl3 import Bits1, mk_bits, DefaultPassGroup
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import config_model_with_cmdline_opts
from src.classifier.sim import frequency_bins, classify
from tools.utils import fixed_bits, mk_test_matrices
from src.classifier.classifier import Classifier
from fixedpt import Fixed


def configure(
    model: Classifier, cutoff_freq: int, cutoff_mag: Fixed, sampling_freq: int
):
    model.cutoff_freq.msg @= cutoff_freq
    model.cutoff_mag.msg @= fixed_bits(cutoff_mag)
    model.sampling_freq.msg @= sampling_freq
    model.cutoff_freq.val @= 1
    model.cutoff_mag.val @= 1
    model.sampling_freq.val @= 1
    model.sim_tick()

    # Wait for the model to be ready
    while True:
        done = True

        if model.cutoff_freq.rdy:
            model.cutoff_freq.val @= 0
        else:
            done = False

        if model.cutoff_mag.rdy:
            model.cutoff_mag.val @= 0
        else:
            done = False

        if model.sampling_freq.rdy:
            model.sampling_freq.val @= 0
        else:
            done = False

        model.sim_tick()

        if done:
            break


def check(model: Classifier, values: list[Fixed], expected: bool):
    for i, value in enumerate(values):
        model.recv_msg[i] @= fixed_bits(value)
    print(values)
    model.recv_val @= 1
    model.send.rdy @= 1
    model.sim_tick()

    while True:
        done = True
        if model.recv_rdy:
            model.recv_val @= 0
        else:
            done = False

        if model.send.val:
            assert model.send.msg == Bits1(expected)
        else:
            done = False

        model.sim_tick()

        if done:
            break


# -------------------------------------------------------------------------
# Tests
# -------------------------------------------------------------------------
@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "n_samples": [4, 16, 32],
            "fp_spec": [
                (16, 8),
                (32, 16),
            ],
            "sampling_freq": [44100, 44800],
            "cutoff_mag": [0.33, 1, 63.32],
            "cutoff_freq": [0, 1000, 1400, 10000],
        }
    )
)
def test_classifier(p, cmdline_opts):
    # Instantiate and elaborate the model
    dut = Classifier(*p.fp_spec, 16, p.n_samples)
    dut = config_model_with_cmdline_opts(dut, cmdline_opts, duts=[])
    dut.apply(DefaultPassGroup(linetrace=False))
    dut.sim_reset()

    cutoff_mag = Fixed(p.cutoff_mag, True, *p.fp_spec)

    # Configure the model
    configure(
        dut,
        p.cutoff_freq,
        cutoff_mag,
        p.sampling_freq,
    )

    # find first bin above the cutoff frequency
    freq_bins = frequency_bins(p.sampling_freq, p.n_samples)
    print(freq_bins)
    cutoff_i = None
    for i, freq in enumerate(freq_bins):
        if freq > p.cutoff_freq:
            cutoff_i = i
            break

    if cutoff_i is None:
        # There are no bins above the cutoff frequency
        # so the classification will be zero even if the input is above the cutoff
        above_cutoff_input = [
            Fixed(p.cutoff_mag * random.uniform(-2, 2), 1, *p.fp_spec)
            for _ in range(p.n_samples)
        ]
        above_cutoff_expected = Bits1(0)

        check(dut, above_cutoff_input, above_cutoff_expected)
    else:
        # There are bins above the cutoff frequency
        # Set all of them to be below the cutoff except one
        above_cutoff_input = [
            Fixed(p.cutoff_mag * random.uniform(-1, 1), 1, *p.fp_spec)
            for _ in range(p.n_samples)
        ]

        above_cutoff_input[random.randint(cutoff_i, p.n_samples - 1)] = Fixed(
            p.cutoff_mag * random.uniform(1, 2) * random.choice([-1, 1]), 1, *p.fp_spec
        )
        above_cutoff_expected = Bits1(1)

        check(dut, above_cutoff_input, above_cutoff_expected)

        # Generate high magnitude input below the cutoff frequency but not above
        below_cutoff_input = [
            Fixed(p.cutoff_mag * random.uniform(-1, 1), 1, *p.fp_spec)
            for _ in range(p.n_samples)
        ]

        below_cutoff_input[random.randint(0, cutoff_i - 1)] = Fixed(
            p.cutoff_mag * random.uniform(1, 2) * random.choice([-1, 1]), 1, *p.fp_spec
        )

        below_cutoff_expected = Bits1(0)

        check(dut, below_cutoff_input, below_cutoff_expected)

    # Now do a bunch of random tests
    for _ in range(100):
        d = [
            Fixed(p.cutoff_mag * random.uniform(-2, 2), 1, *p.fp_spec)
            for _ in range(p.n_samples)
        ]

        expected = classify(d, p.cutoff_freq, cutoff_mag, p.sampling_freq)

        check(dut, d, expected)
