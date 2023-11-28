# =========================================================================
# conftest
# =========================================================================
import linecache
import signal
import pytest
import random
from os import path
import os, psutil
import numpy as np
import subprocess
from tempfile import NamedTemporaryFile
from glob import glob
import sys
import logging
import logging.handlers
import gc
import tracemalloc


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

    parser.addoption(
        "--cleanup-build",
        action="store_true",
        help="Cleanup the build directory after each test case. Used in github actions.",
    )

    parser.addoption(
        "--log-memory",
        action="store_true",
        help="Log the memory usage of the process after each test case.",
    )


def pytest_configure():
    """
    Configures pytest logging to output each worker's log messages
    to its own worker log file and to the console.
    """
    # Determine worker id
    # Also see: https://pytest-xdist.readthedocs.io/en/latest/how-to.html#creating-one-log-file-for-each-worker
    worker_id = os.environ.get("PYTEST_XDIST_WORKER", default="gw0")

    # Create logs folder
    logs_folder = os.environ.get("LOG_FOLDER", default=None)
    if logs_folder is None:
        logs_folder = "log"
    else:
        logs_folder = f"log_{logs_folder}"
    os.makedirs(logs_folder, exist_ok=True)

    # Create file handler to output logs into corresponding worker file
    log_handler = logging.handlers.RotatingFileHandler(
        f"{logs_folder}/worker_{worker_id}.log",
        mode="a",
        maxBytes=5 * 1024 * 1024,
        backupCount=2,
        encoding=None,
        delay=0,
    )
    log_handler.setFormatter(
        logging.Formatter(
            fmt="{asctime} {levelname}:{name}:{lineno}:{message}",
            style="{",
        )
    )

    # Configure logging
    logger = logging.getLogger()
    logger.addHandler(log_handler)


@pytest.fixture(scope="function", autouse=True)
def log_test_name_at_start(request):
    """
    Before starting a test, log its name.
    This makes it easier to retrieve the logs for a specific test.
    """
    logging.info("=" * 20 + request.node.nodeid + "=" * 20)


@pytest.fixture(autouse=True)
def change_test_dir(request, monkeypatch):
    buildfolder = request.config.getoption("--build-dir")
    if buildfolder is None:
        # If no buildfolder is specified, use `build`
        buildfolder = "build"
    else:
        # If a buildfolder is specified, prefix it with `build_` if necessary
        if not buildfolder.startswith("build"):
            buildfolder = f"build_{buildfolder}"
    worker_id = os.environ.get("PYTEST_XDIST_WORKER")
    if worker_id is not None:
        # If we are running multiple threads, give each one a new buildfolder
        buildfolder = path.join(buildfolder, worker_id)

    """Change the working directory to the build directory."""
    wd = path.join(request.config.rootdir, buildfolder)
    os.makedirs(wd, exist_ok=True)

    monkeypatch.chdir(wd)


@pytest.fixture(autouse=True)
def fix_randseed():
    """Set the random seed prior to each test case."""
    random.seed(0xDEADBEEF)
    np.random.seed(0xDEADBEEF)


@pytest.fixture(autouse=True)
def build_cleanup(request):
    """Cleanup the build directory after each test case."""
    yield

    if request.config.getoption("--cleanup-build"):
        cwd = os.getcwd()
        # Extra check to make double sure we are in the build directory and don't remove random files
        if path.split(cwd)[1].startswith("build"):
            subprocess.run(["rm", "-rf", *glob("*")], cwd=cwd)
            logging.info(f"removed files in {os.getcwd()}", file=sys.stderr)
        else:
            logging.info(f"skipped cleanup in {os.getcwd()}", file=sys.stderr)


# Display the top memory-allocating lines
def display_top(snapshot, key_type="traceback", limit=3):
    snapshot = snapshot.filter_traces(
        (
            tracemalloc.Filter(
                False, "<frozen importlib._bootstrap>", all_frames=False
            ),
            tracemalloc.Filter(False, "<unknown>", all_frames=False),
            tracemalloc.Filter(False, tracemalloc.__file__, all_frames=True),
        )
    )

    top_stats = snapshot.statistics("traceback")

    log = f"\nTop {limit} lines\n"
    for index, stat in enumerate(top_stats[:limit], 1):
        log += f"\t#{index}: {stat.size / 1024:.2f} KiB\n"
        for frame in stat.traceback.format():
            log += f"\t\t{frame}\n"
    other = top_stats[limit:]
    if other:
        size = sum(stat.size for stat in other)
        log += f"\t{len(other)} other: {size / 1024:.2f} KiB\n"
    total = sum(stat.size for stat in top_stats)
    logging.debug(log)
    logging.info(f"Total allocated size: {total / 1024:.2f} KiB\n")


@pytest.fixture(scope="session", autouse=True)
def start_tb(request):
    """Start the testbench."""
    if request.config.getoption("--log-memory"):
        tracemalloc.start(25)


@pytest.fixture(autouse=True)
def log_memory(start_tb, request):
    """Log the memory usage of the process after each test case."""
    if request.config.getoption("--log-memory"):
        # tracemalloc.clear_traces()

        yield

        snapshot = tracemalloc.take_snapshot()
        display_top(snapshot, limit=10)

        gc.collect()

        log = "Garbage Collection Stats:\n"
        for generation, stats in enumerate(gc.get_stats()):
            log += f"\tGeneration {generation}:\n"
            log += f"\t\tstats: {stats}\n"
        log += f"\ttracking {len(gc.get_objects())} objects.\n"
        logging.info(log)
        gc.unfreeze()
    else:
        yield


@pytest.fixture()
def dump_asm(request):
    """Dump Assembly File for each test."""
    return request.config.getoption("--dump-asm")


# Pytest fixture to allow python tests to access testfloat_gen.
# Returns a list of lists, where each inner list is a row of numbers referring to the arguments of the test case.
@pytest.fixture()
def testfloat_gen(request):
    def testfloat_gen(func, level=1, seed=0xDEADBEEF, n=None, extra_args=""):
        tfile = NamedTemporaryFile()
        dir, file = path.split(tfile.name())

        args_n = "" if n is None else f"-n {n}"
        args = f"-seed {seed} -level {level} {args_n}{extra_args}"

        # Run the testfloat generator
        testfloat_gen_cmd = f"make testfloat_gen FUNC={func} BUILD_DIR={dir} OUTPUT_FILE={file} EXTRA_ARGS='{args}'"
        testfloat_gen_proc = subprocess.Popen(testfloat_gen_cmd, start_new_session=True)

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
        testfloat_gen = []
        with open(tfile.name(), "r") as f:
            for line in f:
                testfloat_gen.append([int(x, 16) for x in line.split()])

        tfile.close()

    return testfloat_gen
