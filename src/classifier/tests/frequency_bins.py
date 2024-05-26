from src.classifier.helpers.frequency_bins import FrequencyBins
from pymtl3.stdlib.test_utils import run_test_vector_sim
from pymtl3 import mk_bits
import pytest
from tools.utils import mk_test_matrices, fixed_bits
from src.classifier.sim import frequency_bins
from fixedpt import Fixed


def gen_frequency_bins(
    sampling_freq: int, n_samples: int, bit_width: int, decimal_pt: int
):
    print(
        [
            fixed_bits(x)
            for x in frequency_bins(sampling_freq, n_samples, bit_width, decimal_pt)
        ]
    )
    return [
        (
            "sampling_freq "
            + " ".join([f"frequency_out[{i}]*" for i in range(n_samples)])
        ),
        [mk_bits(bit_width)(sampling_freq)]
        + [
            fixed_bits(x)
            for x in frequency_bins(sampling_freq, n_samples, bit_width, decimal_pt)
        ],
    ]


@pytest.mark.parametrize(
    *mk_test_matrices(
        {
            "sampling_freq": [44800, 128],
            "n_samples": [4, 8, 16, 32],
        },
    )
)
def test(cmdline_opts, p):
    run_test_vector_sim(
        FrequencyBins(p.n_samples, 32, 16),
        gen_frequency_bins(p.sampling_freq, p.n_samples, 32, 16),
        cmdline_opts,
    )
