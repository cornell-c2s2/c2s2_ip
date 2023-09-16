# Adding executables to your `PATH` environment variable

## Windows

1. Open `Control Panel` and search for `environment variables` in the search bar.
2. Click on `Edit environment variables for your account`. In the list, look for an environment variable named `Path`.
3. Select it and click `edit...`.
4. Select an empty row and type in `C:/path/to/bin`, where `C:/path/to/bin` is the path to the folder containing your executable.

## MacOS and Linux
Edit your `~/.bash_profile` file (on MacOS) or your `~/.bashrc` file (on Linux) and add the following line:
```sh
export PATH="path/to/bin:$PATH"
```
Replace `path/to/bin` with the path to the folder containing your executable.