# =========================================================================
# Crossbar_test
# =========================================================================

import pytest
from src.crossbars.blocking import BlockingCrossbarWrapper


# Some basic test cases
@pytest.mark.skip(reason="Not implemented yet")
@pytest.mark.parametrize(
    "bit_width, n_inputs, n_outputs, control_bit_width, cmds, expectation",
    [(4, 2, 2, 2, [], [])],  # 2x2 crossbar
)
def test_basic(
    bit_width, n_inputs, n_outputs, control_bit_width, cmds: list, expectation
):
    pass
