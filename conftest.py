# =========================================================================
# conftest
# =========================================================================

import pytest
import random
from os import path
import os
import sys


def pytest_load_initial_conftests(args):
    if "xdist" in sys.modules:  # pytest-xdist plugin detected
        # group tests by file
        args[:] = ["--dist", "loadfile"] + args


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
    buildfolder = request.config.getoption("--build-dir")
    worker_id = os.environ.get("PYTEST_XDIST_WORKER")
    if worker_id is not None:
        # If we are running multiple threads, give each one a new buildfolder
        buildfolder = f"{buildfolder}_{worker_id}"

    """Change the working directory to the build directory."""
    wd = path.join(request.config.rootdir, buildfolder)
    os.makedirs(wd, exist_ok=True)

    monkeypatch.chdir(wd)


@pytest.fixture()
def dump_asm(request):
    """Dump Assembly File for each test."""
    return request.config.getoption("--dump-asm")
