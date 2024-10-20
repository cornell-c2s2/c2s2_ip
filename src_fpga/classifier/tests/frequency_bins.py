from src_fpga.classifier.helpers.frequency_bins import FrequencyBins
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3 import mk_bits
import pytest
from tools.utils import mk_test_matrices, fixed_bits
from src_fpga.classifier.sim import frequency_bins
from fixedpt import Fixed


def gen_frequency_bins(sampling_freq: int, n_samples: int, bit_width: int):
    bits = mk_bits(bit_width)

    print([bits(x) for x in frequency_bins(sampling_freq, n_samples)])
    return [
        (
            "sampling_freq "
            + " ".join([f"frequency_out[{i}]*" for i in range(n_samples)])
        ),
        [bits(sampling_freq)]
        + [bits(x) for x in frequency_bins(sampling_freq, n_samples)],
    ]


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "sampling_freq": [44800, 44100],
            "n_samples": [4, 8, 16, 32],
            "bit_width": [16, 32],
        },
    )
)
def test(cmdline_opts, p):
    run_test_vector_sim(
        FrequencyBins(p.n_samples, p.bit_width),
        gen_frequency_bins(p.sampling_freq, p.n_samples, p.bit_width),
        cmdline_opts,
    )
