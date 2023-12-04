source ~/.bashrc

# Run setup-c2s2.sh if we are on the ecelinux machine
if [ -f /classes/c2s2/setup-c2s2.sh ]; then
  source setup-c2s2.sh
fi

conda activate ./venv

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )" # get the directory of this file

export PYTHONPATH=$PYTHONPATH:$DIR/..

mkdir -p $DIR/bin
export PATH=$PATH:$DIR/bin

# link tools/flow/main.py to tools/bin/caravel
rm -f $DIR/bin/caravel
ln -sf $DIR/flow/main.py $DIR/bin/caravel


echo -e "\033[0;32mC2S2 Workspace Initialized.\033[0m"
