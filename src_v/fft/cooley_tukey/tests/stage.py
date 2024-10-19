import pytest
import random
import math
from pymtl3.stdlib import stream
from pymtl3.stdlib.test_utils import run_sim
from pymtl3 import mk_bits, Component
from tools.utils import mk_test_matrices, cfixed_bits, cmp_exact, mk_cmp_approx
from src.fft.cooley_tukey.helpers.stage import StageWrapper
from fixedpt import Fixed, CFixed
from src.fft.cooley_tukey.sim import fft_stage


# -------------------------------------------------------------------------
# TestHarness
# -------------------------------------------------------------------------
class TestHarness(Component):
    def construct(s, BIT_WIDTH: int, DECIMAL_PT: int, N_SAMPLES: int, STAGE_FFT: int):
        # Instantiate models

        s.src = stream.SourceRTL(mk_bits(BIT_WIDTH))
        s.sink = stream.SinkRTL(mk_bits(BIT_WIDTH))
        s.dut = StageWrapper(
            BIT_WIDTH,
            DECIMAL_PT,
            N_SAMPLES,
            STAGE_FFT,
        )

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


def check_fft_stage(
    bit_width: int,
    decimal_pt: int,
    n_samples: int,
    stage: int,
    cmdline_opts: dict,
    src_delay: int,
    sink_delay: int,
    inputs: list[list[CFixed]],
    outputs: list[list[CFixed]],
) -> None:
    """
    Check the FFT Stage implementation.

    Args:
        bit_width (int): Number of bits.
        decimal_pt (int): Number of decimal points.
        n_samples (int): Number of samples.
        stage (int): Stage of the FFT.
        cmdline_opts (dict): Command line options.
        src_delay (int): Source delay.
        sink_delay (int): Sink delay.
        inputs (list[list[CFixed]]): List of samples to send.
        outputs (list[list[CFixed]]): List of expected output samples.

    Returns:
        bool: True if the test passes, False otherwise.
    """
    assert len(inputs) == len(outputs)
    assert all(len(x) == n_samples for x in inputs)
    assert all(len(x) == n_samples for x in outputs)

    model = TestHarness(bit_width, decimal_pt, n_samples, stage)

    # Convert inputs and outputs into a single list of bits
    inputs = [cfixed_bits(x) for sample in inputs for x in sample]
    outputs = [cfixed_bits(x) for sample in outputs for x in sample]

    # Flatten the lists so that we get [real, imag, real, imag]
    inputs = sum(map(list, inputs), [])
    outputs = sum(map(list, outputs), [])

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

    run_sim(model, cmdline_opts, duts=["dut.dut"], print_line_trace=False)


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(8, 0), (16, 8)],
            "n_samples": [8, 32],
        },
        {
            "fp_spec": [(16, 4)],
            "n_samples": [128, 256],
            "slow": True,
        },
    )
)
def test_dc(cmdline_opts, p):
    """
    Simulates what a DC signal would look like for every stage of an FFT.

    Example (8 point):

    DC Input looks like
        1, 1, 1, 1, 1, 1, 1, 1
    Stage 1 transforms it to
        2, 0, 2, 0, 2, 0, 2, 0
    Stage 2 transforms it to
        4, 0, 0, 0, 4, 0, 0, 0
    Stage 3 transforms it to
        8, 0, 0, 0, 0, 0, 0, 0
    This is the expected FFT Output!
    """

    n_stages = int(math.log2(p.n_samples))

    # Generates the input to the nth stage for an n_samples FFT
    # given DC as an initial input
    def gen_dc(n_samples: int, stage: int) -> list[CFixed]:
        signal = sum(
            [
                [2**stage] + [0] * (2 ** (stage) - 1)
                for _ in range(int(n_samples / (2**stage)))
            ],
            [],
        )
        return [CFixed((x, 0), *p.fp_spec) for x in signal]

    for stage in range(n_stages):
        # Calculate the expected inputs and outputs
        inputs = gen_dc(p.n_samples, stage)
        outputs = gen_dc(p.n_samples, stage + 1)

        # Run the test
        check_fft_stage(
            *p.fp_spec,
            p.n_samples,
            stage,
            cmdline_opts,
            src_delay=0,
            sink_delay=0,
            inputs=[inputs],
            outputs=[outputs],
        )


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "fp_spec": [(32, 16), (16, 8)],
            "n_samples": [8, 64],
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

    # Generate random inputs
    inputs = [
        [CFixed((1, 0), *p.fp_spec) for __ in range(p.n_samples)]
        for _ in range(p.input_num)
    ]

    for stage in range(int(math.log2(p.n_samples))):
        # Generate the expected outputs
        outputs = [fft_stage(x, stage, *p.fp_spec, p.n_samples) for x in inputs]
        print(inputs)
        print(outputs)

        # Run the test
        check_fft_stage(
            *p.fp_spec,
            p.n_samples,
            stage,
            cmdline_opts,
            src_delay=0,
            sink_delay=0,
            inputs=inputs,
            outputs=outputs,
        )
