# =========================================================================
# conftest
# =========================================================================

import signal
import pytest
import random
from os import path
import os
import numpy as np
import subprocess
from tempfile import TemporaryDirectory


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
        default=None,
        help="Build directory to generate files in.",
    )


@pytest.fixture(autouse=True)
def fix_randseed():
    """Set the random seed prior to each test case."""
    random.seed(0xDEADBEEF)
    np.random.seed(0xDEADBEEF)


@pytest.fixture(autouse=True)
def change_test_dir(request, monkeypatch):
    buildfolder = request.config.getoption("--build-dir")
    if buildfolder is None:
        # If no buildfolder is specified, use `build`
        buildfolder = "build"
    else:
        # If a buildfolder is specified, prefix it with `build_`
        buildfolder = f"build_{buildfolder}"
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


# Pytest fixture to allow python tests to access testfloat_gen.
# Returns a list of lists, where each inner list is a row of numbers referring to the arguments of the test case.
@pytest.fixture()
def testfloat_gen(request):
    root_dir = request.config.rootdir

    def testfloat_gen(func, level=1, seed=0xDEADBEEF, n=None, extra_args=""):
        nonlocal root_dir

        with TemporaryDirectory() as dir:
            output_file = "testfloat_gen"
            args_n = "" if n is None else f"-n {n}"
            args = f"-seed {seed} -level {level} {args_n}{extra_args}"

            # Run the testfloat generator
            testfloat_gen_cmd = [
                "make",
                "testfloat_gen",
                f"FUNC={func}",
                f"BUILD_DIR={dir}",
                f"OUTPUT_FILE={output_file}",
                f"EXTRA_ARGS={args}",
            ]
            testfloat_gen_proc = subprocess.Popen(
                testfloat_gen_cmd,
                start_new_session=True,
                cwd=root_dir,
                stdout=subprocess.DEVNULL,
            )

            # Wait for the testfloat generator to finish
            testfloat_gen_timeout = 120
            try:
                testfloat_gen_proc.wait(timeout=testfloat_gen_timeout)
            except subprocess.TimeoutExpired:
                print(
                    f"Testfloat generator timed out after {testfloat_gen_timeout} seconds."
                )
                os.killpg(os.getpgid(testfloat_gen_proc.pid), signal.SIGTERM)
                return None

            # Read the testfloat generator output
            data = []
            with open(path.join(dir, output_file), "r") as f:
                for line in f:
                    data.append([int(x, 16) for x in line.split()])
        return data

    return testfloat_gen
