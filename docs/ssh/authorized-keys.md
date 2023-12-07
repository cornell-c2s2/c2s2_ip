# Logging into `c2s2-dev` without your password

When logging into the `c2s2-dev` by default, you will need to type in your cornell password in order to get authorization. This is slow and won't work with some of our automated scripts, which require ssh access.

To get around this, you need to add your ssh key (**the public one, not the private one**) to the `~/.ssh/authorized_keys` file.

## Finding your public key
Your public and private keys can be found in your local `~/.ssh` directory (in windows, this is `C:\Users\<your user>\.ssh`). Find the file that ends in `.pub` and copy its contents into a file called `~/.ssh/authorized_keys` **on c2s2_dev**. This file will not exist by default, so you may have to create it yourself.

Next, run `chmod 600 ~/.ssh/authorized_keys` to set the permissions of the file up properly.

To confirm this works, hit `Ctrl+Shift+P` and select `Reload Window`, and, with luck, you should be logged in without having to type anything!