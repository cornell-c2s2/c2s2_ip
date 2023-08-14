#=========================================================================
# conftest
#=========================================================================

import pytest
import random

def pytest_addoption(parser):

  parser.addoption( "--dump-asm", action="store_true",
                    help="dump asm file for each test" )

  parser.addoption( "--dump-bin", action="store_true",
                    help="dump binary file for each test" )

@pytest.fixture(autouse=True)
def fix_randseed():
  """Set the random seed prior to each test case."""
  random.seed(0xdeadbeef)

@pytest.fixture()
def dump_asm(request):
  """Dump Assembly File for each test."""
  return request.config.getoption("--dump-asm")

