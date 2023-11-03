# Using `pytest`

Our verilog simulation tests are written using `pymtl3`, and run using `pytest`. Because `pytest` is set up slightly differently here than you might be used to in your ECE courses, **please read carefully even if you have experience using `pymtl3` from class!**

## Build Directories
No matter where you run `pytest` in this repository, by default all files will be generated in the `c2s2_ip/build` directory. This includes `--dump-vcd` files, all the verilated files, etc. 

If you want to customize what build directory to write to, use `pytest --build-dir name`. This will instead generate your files in `c2s2_ip/build_name`. 

### `pytest-xdist` Build Directories
Running pytest with `n` workers (threads) will create `n` build directories, each named `build_gw<i>` where `i` is the index of the worker (from `0` to `n-1`). This is done so that multiple threads trying to verilate the same model and reading/writing the same files doesn't lead to problems. 

*Note: If you have a custom directory, say `build_1`, files will be generated under `build_1_gw<i>` instead.*

## Command-line Arguments

This is a short introduction to some of `pytest`'s command line arguments. `Pytest`'s [documentation](https://docs.pytest.org/en/6.2.x/usage.html) contains some useful information if you want specifics on all its arguments.

1. Selecting certain files (or folders) to be run is as simple as `pytest path/to/test`. This will run only all the files in folder `test` (or file). This is useful if you want to test specific modules without running the whole suite.
2. `-k "name_of_test"` will allow you to select tests by their name. For example, if you have a function called `test_example`, `pytest -k example` will run this test, but not another test called `test_something_else`.
3. `-v` will enable verbose mode, which means each test will be printed with its name when it is run, rather than just a dot.
4. `-tb=<auto, long, short, line, native, no>` will affect how traceback is printed. Further details are available [here](https://docs.pytest.org/en/6.2.x/usage.html#modifying-python-traceback-printing).
5. `-m slow` will run all tests marked slow, and `-m "not slow"` will run tests not marked slow (pytest `mark`s are described in [this section](#marking-tests)).

### `pytest-xdist` Arguments

`pytest-xdist` is an add-on to pytest that allows us to run tests in parallel. This is especially useful when running tests for large blocks or the entire suite, as it can significantly speed up test times. Your `ecelinux` machine has `10` cores, so you can expect about `10` times speedup on your tests using `xdist`!

In order to enable multi-core testing, run `pytest -n auto` (or `-n <number of threads>` if you want). This will collect all your tests and split them among all your CPUs. This is elaborated further in [this section](#pytest-xdist-build-directories), but each thread will be given its own build directory, in order to prevent read/write data races. This means that the generated test files will might be split among multiple directories.

## Marking Tests
Tests can be marked with custom tags in `pytest`, using the syntax `@pytest.mark.name` to mark a test with `name`. This lets us filter what tests we want to run easily. Currently, tests can be marked with the `slow` attribute to indicate that they will take a while to run. This is used by the github actions scripts running on push, one of which runs only `not slow` tests to give quick feedback on whether the suite is likely to pass all tests.