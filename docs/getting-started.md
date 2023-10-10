# Getting Started
Hello, and welcome to C2S2!

To get started, you'll want to make sure you have access to the following things:
* [C2S2's Confluence Page](https://confluence.cornell.edu/display/c2s2)
* Added to C2S2's Github Organization
  * Go to your github profile and look in the bottom left, under **Organizations**. If C2S2's logo appears there, you're in!
* [C2S2's ecelinux Machine](https://confluence.cornell.edu/display/c2s2/Accessing+the+Team+Server)
  * Follow the tutorial linked above, if anything doesn't work, let us know!

If for some reason you don't have access to any of these, contact your subteam leads.

## Installing VSCode and connecting to `c2s2-dev`

Next, you'll want to get your working environment set up. If you don't already have experience with `git` and `github`, we recommend taking a look at the [Git/Github Primer](https://confluence.cornell.edu/pages/viewpage.action?pageId=476108648) on confluence.

1. First, you'll need to install VSCode (if you haven't already). VSCode can be downloaded [here](https://code.visualstudio.com/download).
2. Install the `Remote - SSH` extension. If you need help installing extensions, VSCode has a useful tutorial [here](https://code.visualstudio.com/docs/editor/extension-marketplace).
3. Press `Ctrl+Shift+P` and select `Remote-SSH: Connect to Host...`, and type in `your-netid@c2s2-dev.ece.cornell.edu`. Select `Linux` if it asks for your platform.
   * [This tutorial](https://code.visualstudio.com/docs/remote/ssh) has some more details (under the `Connect to a remote host` section).
4. Type in your password when it asks for it, and you should be in!
   *  Remember to run `source setup-c2s2.sh` every time you log in (or add it to your `~/.bashrc` if you know how). If you're interested, the bottom of [this tutorial](https://confluence.cornell.edu/pages/viewpage.action?pageId=476109085) covers what a `~/.bashrc` file is.

## Cloning and Setting Up `c2s2_ip`

Now that you're in your ssh machine, you'll want to get the github repository up and running.
1. First, you'll want to get github set up for your ssh machine. A useful tutorial exists [here](https://confluence.cornell.edu/pages/viewpage.action?spaceKey=c2s2&title=Configuring+GitHub+for+our+server) that describes how to set github up.
2. Navigate to somewhere you'd like your code, and run `git clone git@github.com:cornell-c2s2/c2s2_ip.git`. This will create a folder named `c2s2_ip` with your code.
3. Open `c2s2_ip` as a workspace in VSCode. You can do so in two ways:
   1. Run `code c2s2_ip` in the terminal. This should open a new VSCode window, where you have to log in again.
   2. Click `File > Open Folder` and select the `c2s2_ip` folder.
4. Run `make install` in your terminal. This should install all the required dependencies for the workspace. This includes a few VSCode extensions as well as setting up a `python` virtual environment with all the necessary `pip` packages.
5. Type `Ctrl+Shift+P` and select `Python: Create Environment...`, and select `venv`. Next, select `Use Existing` and in the bottom right you should get that `c2s2_ip/.venv/bin/python` was selected as your default interpreter.
6. Type `Ctrl+Shift+P` and select `Reload Window`. This should activate all the extensions you just installed.
7. Read the [makefile tutorial](make.md) and the [pytest tutorial](pytest.md) to learn more about how to get started making new IP!