from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import (
    run_sim,
    run_test_vector_sim,
    config_model_with_cmdline_opts,
)
from pymtl3.stdlib import stream
from src.tapeins.sp24.tapein1.interconnect import Interconnect
from src.spi.master import SPIMaster


class InterconnectWrapper(Component):
    def construct(s):
        s.master = SPIMaster(nbits=18, ncs=1)
        s.interconnect = Interconnect()

        s.logBitsN = clog2(18) + 1

        s.src = stream.SourceRTL(mk_bits(18))
        s.sink = stream.SinkRTL(mk_bits(18))

        s.pkt_size_src = stream.SourceRTL(mk_bits(s.logBitsN))
        s.freq_src = stream.SourceRTL(mk_bits(3))
        s.cs_src = stream.SourceRTL(mk_bits(1))

        s.pkt_size_src.send //= s.master.packet_size_ifc
        s.freq_src.send //= s.master.freq_ifc
        s.cs_src.send //= s.master.cs_addr_ifc

        s.src.send //= s.master.recv
        s.master.send //= s.sink.recv

        # connect the wires
        s.master.spi_ifc.cs[0] //= s.interconnect.cs
        s.master.spi_ifc.sclk //= s.interconnect.sclk
        s.master.spi_ifc.mosi //= s.interconnect.mosi
        s.interconnect.miso //= s.master.spi_ifc.miso

    def done(s):
        return s.src.done() and s.sink.done()

    def line_trace(s):
        return (
            s.src.line_trace()
            + " > "
            + s.master.line_trace()
            + " > "
            + s.interconnect.line_trace()
            + " > "
            + s.sink.line_trace()
        )


def test_interconnect(cmdline_opts, interval_delay=3):
    model = InterconnectWrapper()

    # Run the model
    model.set_param(
        "top.src.construct",
        msgs=[0b101010101010101010, 0b010101010101010101],
        initial_delay=20,
        interval_delay=interval_delay,
    )

    model.set_param(
        "top.sink.construct",
        msgs=[0x4000, 0x320],
        initial_delay=20,
        interval_delay=interval_delay,
    )

    model.set_param(
        "top.pkt_size_src.construct",
        msgs=[18],
        initial_delay=3,
        interval_delay=interval_delay,
    )

    model.set_param(
        "top.freq_src.construct",
        msgs=[0],
        initial_delay=4,
        interval_delay=interval_delay,
    )

    model.set_param(
        "top.cs_src.construct",
        msgs=[0b0],
        initial_delay=5,
        interval_delay=interval_delay,
    )

    run_sim(model, cmdline_opts)
