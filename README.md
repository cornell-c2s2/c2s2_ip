# c2s2_ip
C2S2_IP is a repository for keeping track of all of C2S2's IP

## Getting Started
For new members, check out [this tutorial](docs/getting-started.md) for some helpful quickstart information.

## Basic Usage
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
