# Installing `svlint`

Note: this is entirely optional; we have an automated github actions script that installs and checks linting, and will leave comments on your pushes.

1. Download [svlint](https://github.com/dalance/svlint/releases) from the latest release (in the `releases` tab). Choose the file that matches your operating system.
2. Unzip the file **somewhere you will be willing to keep it without moving it**.
3. Add the file to your `PATH`. If you don't know how to do that for your operating system, there's a short tutorial [here](./path.md).
4. To check whether this works, open a new terminal window (`cmd` or `powershell` on windows) and type `svlint`. If you get an error like this:
```sh
error: The following required arguments were not provided:
    <FILES>...

USAGE:
    svlint <FILES>...

For more information try --help
```
that means `svlint` was properly installed.

Note: make sure you open a **new** terminal window here, if you try to use an already open window this might not work.
