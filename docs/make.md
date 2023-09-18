# Using `make`

## Creating IP (Blocks)
We use Makefile recipies and Git to help automate a lot of the functionality.

All IP has an associated name, corresponding to the main directory name. To check if an IP name is valid (a.k.a. it doesn't already exist), run
```
make check-ip IP_NAME=<name>
```
(replacing `name` with your desired name)

Once you have verified that the IP name is a valid one, you can create the IP using
```
make new-ip IP_NAME=<name>
```
This will create a new Git branch for the desired IP, a new directory for it, as well as a starter file. 
It will also set the branch's upstream, so that users who are familiar with basic Git without branches can simply use it as normal
with `add`, `commit`, and `push` commands

### `IP_NAME` Conventions

The makefile will attempt to parse your `IP_NAME` into separate words. For example, names like `FFTTwiddleGenerator` will be converted to `fft_twiddle_generator`. This is for a couple reasons:
* So that one member cannot create the `FixedPoint` IP when the `fixed_point` IP already exists (to prevent naming confusion) 
* To make sure folder naming conventions are kept so that python can properly recognize them as module names.

The program will ask for confirmation after attempting to automatically convert your name. If you are ok with the result, type `y` in the command prompt, and then `return`. If not, type `n` and then `return`. 

We recommend typing in `IP_NAME` either
* as a series of lowercase words separated by dashes or underscores (`example-name`)
* or in PascalCase (`ExampleName`).

and to avoid starting words with numbers or using non-alphaneumeric characters.

## `make clean`

Clears all the files in your `build` directory. Useful especially after running `make test`, which can generate tons of files.

## `make lint`
```
make lint
```
Checks all verilog in the repository for whether they follow the linting (code style) guidelines.

This requires `svlint` to be installed and in your `PATH`.

**Note**: Github actions has an automated script that already runs this on push, so installing `svlint` is entirely optional. However, there is a tutorial [here](./svlint.md) on how to do so, if you want to.