# Using `make`

## Creating IP (Blocks)
We use Makefile recipies and Git to help automate a lot of the functionality.

All IP has an associated name, corresponding to the main directory name. To check if an IP name is valid (a.k.a. it doesn't already exist), run
```sh
make check-ip IP=<name>
```
(replacing `name` with your desired name)

Once you have verified that the IP name is a valid one, you can create the IP using
```sh
make new-ip IP=<name>
```
This will create a new Git branch for the desired IP, a new directory for it, as well as a starter file. 
It will also set the branch's upstream, so that users who are familiar with basic Git without branches can simply use it as normal
with `add`, `commit`, and `push` commands

### `IP` Conventions

The makefile will attempt to parse your `IP` into separate words. For example, names like `FFTTwiddleGenerator` will be converted to `fft_twiddle_generator`. This is for a couple reasons:
* So that one member cannot create the `FixedPoint` IP when the `fixed_point` IP already exists (to prevent naming confusion) 
* To make sure folder naming conventions are kept so that python can properly recognize them as module names.

The program will ask for confirmation after attempting to automatically convert your name. If you are ok with the result, type `y` in the command prompt, and then `return`. If not, type `n` and then `return`. 

We recommend typing in `IP` either
* as a series of lowercase words separated by dashes or underscores (`example-name`)
* or in PascalCase (`ExampleName`).

and to avoid starting words with numbers or using non-alphaneumeric characters.

## `make test`
Runs all the tests in the entire test suite.

* An optional `IP="exact_name"` can be used to run the tests in the IP `src/exact_name`.
  * `IP` can also be replaced with `exact_name/tests/test.py` to run a specific file in the `exact_name` ip.

    *Note here that `IP` must be the exact name, and will not go through the parsing described above.*
* A further argument `INCLUDE="expression or expression2"` matches the `-k` argument [in pytest](https://docs.pytest.org/en/6.2.x/usage.html).

We still recommend running `pytest` manually if you want to use the full range of pytest's arguments.

## `make clean`

Clears all the files in your `build` directory. Useful especially after running `make test`, which can generate tons of files.

## `make lint`
Checks all verilog files in the repository for whether they follow the linting (code style) guidelines.

You can select specific IP to check using 
```sh
make lint IP=<name of ip folder>
```

This requires `svlint` to be installed and in your `PATH` as well as requiring `sudo apt-get install moreutils` (which should be the case for your `ecelinux` machine).

**Note**: Github actions has an automated script that already runs this on push, so installing `svlint` is entirely optional. However, there is a tutorial [here](./svlint.md) on how to do so, if you want to.

# Advanced `make` Commands

## `make testfloat_gen`
Runs [testfloat_gen](http://www.jhauser.us/arithmetic/TestFloat-3/doc/testfloat_gen.html) and generates the output in a specified file.

### Usage
```sh
make testfloat_gen FUNC=<func_name> EXTRA_ARGS=<extra_args> OUTPUT_FILE=<output_file> BUILD_DIR=<build_directory>
```