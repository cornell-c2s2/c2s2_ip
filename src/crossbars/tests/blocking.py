# =========================================================================
# Crossbar_test
# =========================================================================

import pytest
from pymtl3 import mk_bits, Component, Bits
from pymtl3.stdlib import stream
from src.crossbars.blocking import BlockingCrossbarWrapper
from src.crossbars.sim import create_crossbar
from pymtl3.stdlib.test_utils import run_sim
import math


# Test harness module
class TestHarness(Component):
    def construct(s, BIT_WIDTH, N_INPUTS, N_OUTPUTS):
        # Instantiate models
        CONTROL_BIT_WIDTH = int(math.log2(N_INPUTS) + math.log2(N_OUTPUTS))
        SPI_BIT_WIDTH = int(1)

        s.control = stream.SourceRTL(mk_bits(CONTROL_BIT_WIDTH))

        s.srcs = [stream.SourceRTL(mk_bits(BIT_WIDTH)) for _ in range(N_INPUTS)]
        s.input_spi = stream.SourceRTL(mk_bits(SPI_BIT_WIDTH))
        s.output_spi = stream.SourceRTL(mk_bits(SPI_BIT_WIDTH))
        s.sinks = [stream.SinkRTL(mk_bits(BIT_WIDTH)) for _ in range(N_OUTPUTS)]
        

        s.dut = BlockingCrossbarWrapper(BIT_WIDTH, N_INPUTS, N_OUTPUTS)
        
        # Connect
        for i in range(N_INPUTS):
            s.srcs[i].send //= s.dut.recv[i]

        for i in range(N_OUTPUTS):
            s.dut.send[i] //= s.sinks[i].recv
        
        s.control.send //= s.dut.control



    def done(s):
        # These are any as the unselected inputs/outputs may not be done
        return any([x.done() for x in s.srcs]) and any([x.done() for x in s.sinks])

    def line_trace(s):
        return (
            " | ".join([x.line_trace() for x in s.srcs])
            + " > "
            + " | ".join([x.line_trace() for x in s.sinks])
        )


# Some basic test cases
@pytest.mark.parametrize(
    "bit_width, n_inputs, n_outputs, config, input_spi, output_spi, inputs",
    [
        (4, 2, 2, (1, 1), 0, 0, [[1, 1], [0, 0], [1, 0]]),  # 2x2 crossbar
        (4, 2, 2, (1, 0), 0, 0, [[1, 1], [0, 0], [1, 0]]),  # 2x2 crossbar
        (4, 2, 2, (1, 1), 0, 1, [[1, 1], [0, 0], [1, 0]]),  # 2x2 crossbar
        (4, 2, 2, (0, 1), 1, 0, [[1, 1], [0, 0], [1, 0]]),  # 2x2 crossbar
        (4, 2, 2, (1, 1), 1, 1, [[1, 1], [0, 0], [1, 0]]),  # 2x2 crossbar
        (4, 2, 2, (1, 1), 0, 0, [[1, 1], [0, 0], [1, 0]]),  # 2x2 crossbar
        (4, 2, 2, (1, 0), 0, 0, [[0, 1], [0, 1], [1, 0]]),  # 2x2 crossbar
    ],
)
def test_basic(
    bit_width,
    n_inputs,
    n_outputs,
    config: tuple[int, int],
    input_spi,
    output_spi,
    inputs: list[list[int]],
    cmdline_opts,
):

    model = TestHarness(bit_width, n_inputs, n_outputs)

    # Generate expected outputs
    sim_xbar, sim_cfg = create_crossbar(bit_width, n_inputs, n_outputs)
    sim_cfg(*config, input_spi, output_spi)
    outputs = [sim_xbar(inp) for inp in inputs]

    control_bit_width = int(math.log2(n_inputs) + math.log2(n_outputs))

    concatted_cfg_msg = mk_bits(control_bit_width)(
        config[0] << int(math.log2(n_outputs)) | config[1]
    )

    # convert to bits types
    inputs = [[mk_bits(bit_width)(x) for x in inp] for inp in inputs]
    outputs = [[mk_bits(bit_width)(x) for x in oup] for oup in outputs]

    model.set_param(
        "top.control.construct",
        msgs=[concatted_cfg_msg],
        initial_delay=1,
        interval_delay=1,
    )

    for i in range(n_inputs):
        print("input", [x[i] for x in inputs])
        model.set_param(
            f"top.srcs[{i}].construct",
            msgs=[x[i] for x in inputs],
            initial_delay=10,
            interval_delay=3,
        )
    for i in range(n_outputs):
        print("output", [x[i] for x in outputs])
        model.set_param(
            f"top.sinks[{i}].construct",
            msgs=[x[i] for x in outputs],
            initial_delay=10,
            interval_delay=3,
        )
    
    model.set_param(
        "top.input_spi.construct",
        msgs=[input_spi],
        initial_delay=10,
        interval_delay=3,
    )

    model.set_param(
        "top.output_spi.construct",
        msgs=[output_spi],
        initial_delay=10,
        interval_delay=3,
    )

    run_sim(model, cmdline_opts, duts=["dut"])