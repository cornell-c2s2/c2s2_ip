# =========================================================================
# conftest
# =========================================================================

import pytest
import random
from os import path
import os


def pytest_addoption(parser):
    parser.addoption(
        "--dump-asm", action="store_true", help="dump asm file for each test"
    )

    parser.addoption(
        "--dump-bin", action="store_true", help="dump binary file for each test"
    )

    parser.addoption(
        "--build-dir",
        action="store",
        default="build",
        help="Build directory to generate files in.",
    )


@pytest.fixture(autouse=True)
def fix_randseed():
    """Set the random seed prior to each test case."""
    random.seed(0xDEADBEEF)


@pytest.fixture(autouse=True)
def change_test_dir(request, monkeypatch):
    """Change the working directory to the src directory."""
    wd = path.join(request.config.rootdir, request.config.getoption("--build-dir"))
    os.makedirs(wd, exist_ok=True)

    monkeypatch.chdir(wd)


@pytest.fixture()
def dump_asm(request):
    """Dump Assembly File for each test."""
    return request.config.getoption("--dump-asm")
