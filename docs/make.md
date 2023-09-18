# Using `make`

## Creating IP (Blocks)
We use Makefile recipies and Git to help automate a lot of the functionality.

All IP has an associated name, corresponding to the main directory name. To check if an IP name is valid (a.k.a. it doesn't already exist), run
```
make check_ip IP_NAME=<name>
```
(replacing `name` with your desired name)

Once you have verified that the IP name is a valid one, you can create the IP using
```
make new_ip IP_NAME=<name>
```
This will create a new Git branch for the desired IP, a new directory for it, as well as a starter file. 
It will also set the branch's upstream, so that users who are familiar with basic Git without branches can simply use it as normal
with `add`, `commit`, and `push` commands

## Linting
```
make lint
```
Checks all files in the repository for whether they follow the linting guidelines.

This requires `svlint` to be installed and in your `PATH`.

Note: Github actions has an automated script that already runs this on push, so installing `svlint` is entirely optional.

There is a tutorial [here](./svlint.md) on how to do so, if you want to.