import pytest
import random
from pymtl3 import mk_bits, Component, Bits
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import run_sim
from src.fft.cooley_tukey.sim import fft as cooley_tukey_fft
from src.fft.pease.sim import fft as pease_fft
from src.fft.cooley_tukey.fft import FFT as HardFFTCooleyTukey
from src.fft.pease.fft import FFT as HardFFTPease
import math
from fixedpt import CFixed, Fixed
from tools.utils import fixed_bits, mk_test_matrices, cmp_exact, mk_cmp_approx
from abc import ABC, abstractmethod
import numpy as np
from src.serdes.deserializer import Deserializer
from src.serdes.serializer import Serializer
from pymtl3.passes.backends.verilog import VerilogTranslationPass


class FFTWrapper(Component):
    def construct(s, BIT_WIDTH: int, DECIMAL_PT: int, N_SAMPLES: int, model: str):
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(BIT_WIDTH))

        # Hook up a deserializer
        s.deserializer = Deserializer(BIT_WIDTH, N_SAMPLES)
        s.recv.msg //= s.deserializer.recv_msg
        s.recv.val //= s.deserializer.recv_val
        s.deserializer.recv_rdy //= s.recv.rdy

        # Hook up a serializer
        s.serializer = Serializer(BIT_WIDTH, N_SAMPLES)
        s.serializer.send_msg //= s.send.msg
        s.serializer.send_val //= s.send.val
        s.send.rdy //= s.serializer.send_rdy

        # Hook up the FFT
        models = {
            "CooleyTukey": HardFFTCooleyTukey,
            "Pease": HardFFTPease,
        }
        s.dut = models[model](BIT_WIDTH, DECIMAL_PT, N_SAMPLES)

        # Hook up the deserializer to the FFT
        for i in range(N_SAMPLES):
            s.deserializer.send_msg[i] //= s.dut.recv_msg[i]

        s.deserializer.send_val //= s.dut.recv_val
        s.dut.recv_rdy //= s.deserializer.send_rdy

        # Hook up the FFT to the serializer
        for i in range(N_SAMPLES):
            s.dut.send_msg[i] //= s.serializer.recv_msg[i]

        s.dut.send_val //= s.serializer.recv_val
        s.serializer.recv_rdy //= s.dut.send_rdy

        s.set_metadata(
            VerilogTranslationPass.explicit_module_name,
            f"{model}FFTWrapper__BIT_WIDTH_{BIT_WIDTH}__DECIMAL_PT_{DECIMAL_PT}__N_SAMPLES_{N_SAMPLES}",
        )

    def line_trace(s):
        return f"{s.deserializer.line_trace()} > {s.dut.line_trace()} > {s.serializer.line_trace()}"


# Test harness module
class TestHarness(Component):
    def construct(s, BIT_WIDTH, DECIMAL_PT, N_SAMPLES, cmp, model):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(
            mk_bits(BIT_WIDTH),
            cmp_fn=cmp,
        )
        s.dut = FFTWrapper(BIT_WIDTH, DECIMAL_PT, N_SAMPLES, model)

        # Connect

        s.src.send //= s.dut.recv
        s.dut.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

    def line_trace(s):
        return (
            s.src.line_trace()
            + " > "
            + s.dut.line_trace()
            + " > "
            + s.sink.line_trace()
        )


# Python interface for the FFT Simulation model-based testing
class FFTInterface(ABC):
    def __init__(self, bit_width, decimal_pt, n_samples):
        self.bit_width = bit_width
        self.decimal_pt = decimal_pt
        self.n_samples = n_samples

    @abstractmethod
    def transform(self, data: list[CFixed]) -> list[CFixed]:
        # Perform the FFT on the given data
        pass


# Version of the FFT simulation that uses a normal numpy FFT algorithm. This is used to verify the Verilog implementation approximately.
class FFTNumpy(FFTInterface):
    def transform(self, data: list[CFixed]) -> list[CFixed]:
        # Convert the data to a list of complex numbers
        d = [complex(x) for x in data]

        # Perform the FFT
        d = np.fft.fft(d, self.n_samples)

        return [CFixed(x, self.bit_width, self.decimal_pt) for x in d]


# Versions of the FFT simulation that uses the exact same algorithm as the Verilog implementation. This is used to verify the Verilog implementation.
class FFTCooleyTukey(FFTInterface):
    def transform(self, data: list[CFixed]) -> list[CFixed]:
        # Use the exact software simulation instead
        return cooley_tukey_fft(data, self.bit_width, self.decimal_pt, self.n_samples)


class FFTPease(FFTInterface):
    def transform(self, data: list[CFixed]) -> list[CFixed]:
        # Use the exact software simulation instead
        return pease_fft(data, self.bit_width, self.decimal_pt, self.n_samples)


def check_fft(
    bit_width: int,
    decimal_pt: int,
    n_samples: int,
    cmdline_opts: dict,
    src_delay: int,
    sink_delay: int,
    comparison_fn: callable,
    model: Component,
    inputs: list[list[Fixed]],
    outputs: list[list[Fixed]],
) -> None:
    """
    Check the FFT implementation.

    Args:
        bit_width (int): Number of bits.
        decimal_pt (int): Number of decimal points.
        n_samples (int): Number of samples.
        cmdline_opts (dict): Command line options.
        src_delay (int): Source delay.
        sink_delay (int): Sink delay.
        comparison_fn (callable): Comparison function.
        model (Component): Hardware FFT model to test.
        inputs (list[list[Fixed]]): List of inputs (only contains the real part of the complex input).
        outputs (list[list[Fixed]]): List of expected outputs (only contains the real part of the complex output).

    Returns:
        bool: True if the test passes, False otherwise.
    """
    assert len(inputs) == len(outputs)
    assert all(len(x) == n_samples for x in inputs)
    assert all(len(x) == n_samples for x in outputs)

    model = TestHarness(bit_width, decimal_pt, n_samples, comparison_fn, model)

    # Convert inputs and outputs into a single list of bits
    inputs = [fixed_bits(x) for sample in inputs for x in sample]
    outputs = [fixed_bits(x) for sample in outputs for x in sample]

    # Run the model
    model.set_param(
        "top.src.construct",
        msgs=inputs,
        initial_delay=src_delay + 3,
        interval_delay=src_delay,
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
        *[
            {"src_delay": [0, 1, 5], "sink_delay": [0, 1, 5], **d}
            for d in [
                {  # 8 point DC
                    "bit_width": 16,
                    "decimal_pt": 8,
                    "n_samples": 8,
                    "inputs": [  # 1, 1, 1, 1, 1, 1, 1, 1
                        [[Fixed(1, True, 16, 8) for _ in range(8)]]
                    ],
                    "outputs": [  # 8, 0, 0, 0, 0, 0, 0, 0
                        [
                            [Fixed(8, True, 16, 8)]
                            + [Fixed(0, True, 16, 8) for _ in range(7)]
                        ]
                    ],
                    "cmp_fn": cmp_exact,
                    "model": ["Pease", "CooleyTukey"],
                },
                {  # 8 point alternating
                    "bit_width": 16,
                    "decimal_pt": 8,
                    "n_samples": 8,
                    "inputs": [  # 1, 0, 1, 0, 1, 0, 1, 0
                        [
                            sum(
                                [
                                    [Fixed(1, True, 16, 8), Fixed(0, True, 16, 8)]
                                    for _ in range(4)
                                ],
                                [],
                            )
                        ]
                    ],
                    "outputs": [  # 4, 0, 0, 0, 4, 0, 0, 0
                        [
                            sum(
                                [
                                    [Fixed(4, True, 16, 8)]
                                    + [Fixed(0, True, 16, 8) for _ in range(3)]
                                    for _ in range(2)
                                ],
                                [],
                            )
                        ]
                    ],
                    "cmp_fn": cmp_exact,
                    "model": ["Pease", "CooleyTukey"],
                },
            ]
        ]
    )
)
def test_manual(cmdline_opts, p):
    # Test the FFT implementation with manually calculated inputs and outputs
    check_fft(
        p.bit_width,
        p.decimal_pt,
        p.n_samples,
        cmdline_opts,
        src_delay=0,
        sink_delay=0,
        comparison_fn=p.cmp_fn,
        model=p.model,
        inputs=p.inputs,
        outputs=p.outputs,
    )


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(16, 8), (32, 16)],
            "n_samples": [8, 16, 32],
            "model": ["Pease", "CooleyTukey"],
        },
        {
            "fp_spec": [(16, 8), (32, 16)],
            "n_samples": [64, 128],
            "model": ["Pease", "CooleyTukey"],
            "slow": True,
        },
    )
)
def test_single_freqs(
    cmdline_opts, p
):  # Tests the FFT implementation for all divisible single frequency inputs.
    # Get the number of stages
    n_stages = int(math.log2(p.n_samples))

    assert 1 << n_stages == p.n_samples

    """
    Generate the inputs:
        For every divisible frequency, generate the input signal with the given frequency.

    For example:
        8 Point FFT Inputs:
            1. 8Hz = 1, 1, 1, 1, 1, 1, 1, 1  ->  8, 0, 0, 0, 0, 0, 0, 0
            2. 4Hz = 1, 0, 1, 0, 1, 0, 1, 0  ->  4, 0, 0, 0, 4, 0, 0, 0
            3. 2Hz = 1, 0, 0, 0, 1, 0, 0, 0  ->  2, 0, 2, 0, 2, 0, 2, 0
            4. 1Hz = 1, 0, 0, 0, 0, 0, 0, 0  ->  1, 0, 1, 0, 1, 0, 1, 0
    """

    inputs = []
    outputs = []

    for i in range(0, n_stages + 1):
        inp_wavelength = 1 << i

        # Generate the input signal
        inputs.append(
            sum(
                [
                    [Fixed(1, True, *p.fp_spec)]  # 1
                    + [Fixed(0, True, *p.fp_spec)]
                    * (inp_wavelength - 1)  # pad rest with zeros
                    for _ in range(p.n_samples // inp_wavelength)
                ],
                [],
            )
        )

        out_wavelength = p.n_samples // inp_wavelength

        # Generate the expected output signal
        outputs.append(
            sum(
                [
                    [Fixed(out_wavelength, True, *p.fp_spec)]
                    + [Fixed(0, True, *p.fp_spec)] * (out_wavelength - 1)
                    for _ in range(inp_wavelength)
                ],
                [],
            )
        )

    check_fft(
        p.fp_spec[0],
        p.fp_spec[1],
        p.n_samples,
        cmdline_opts,
        src_delay=0,
        sink_delay=0,
        comparison_fn=cmp_exact,
        model=p.model,
        inputs=inputs,
        outputs=outputs,
    )


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16), (16, 8)],
            "model_spec": sum(
                [
                    [
                        (
                            hard,  # Hardware model
                            FFTNumpy,  # Model (must implement FFTInterface)
                            "approx",
                        ),
                        (hard, soft, "exact"),  # Model (must implement FFTInterface)
                    ]
                    for (hard, soft) in [
                        (
                            "CooleyTukey",
                            FFTCooleyTukey,
                        ),
                        ("Pease", FFTPease),
                    ]
                ],
                [],
            ),
            "n_samples": [8, 16, 32, 64],
            "input_mag": [1, 10],  # Maximum magnitude of the input signal
            "input_num": [1, 10],  # Number of random inputs to generate
            "seed": list(range(2)),  # Random seed
            "slow": True,
        }
    )
)
def test_model(cmdline_opts, p):
    random.seed(
        random.random() + p.seed
    )  # Done so each test has a deterministic but different random seed

    # Test the FFT implementation with a specified model

    # Create the model
    hard, soft, cmp = p.model_spec
    model: FFTInterface = soft(p.fp_spec[0], p.fp_spec[1], p.n_samples)

    # Generate random inputs
    inputs = [
        [
            CFixed((random.uniform(-p.input_mag, p.input_mag), 0), *p.fp_spec)
            for i in range(p.n_samples)
        ]
        for _ in range(p.input_num)
    ]

    # Generate the expected outputs
    outputs = [model.transform(x) for x in inputs]
    # Convert to Fixed by keeping only the real part
    inputs = [[x.real for x in sample] for sample in inputs]
    outputs = [[x.real for x in sample] for sample in outputs]

    def test(x: Bits, y: Bits):
        if cmp == "approx":
            x = x.int()
            y = y.int()
            return abs(x - y) / (2 ** p.fp_spec[1]) < 0.1 * p.input_mag
        else:
            return cmp_exact(x, y)

    # Run the test
    check_fft(
        p.fp_spec[0],
        p.fp_spec[1],
        p.n_samples,
        cmdline_opts,
        src_delay=0,
        sink_delay=0,
        comparison_fn=test,
        model=hard,
        inputs=inputs,
        outputs=outputs,
    )
